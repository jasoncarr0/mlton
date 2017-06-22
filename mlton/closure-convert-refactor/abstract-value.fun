(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor AbstractValue (S: ABSTRACT_VALUE_STRUCTS): ABSTRACT_VALUE =
struct

open S
open Sxml

structure Dset = DisjointSet

local
structure Lambda =
   struct
      datatype t = Lambda of {lambda: Sxml.Lambda.t,
                              hash: Word.t}

      val newHash = Random.word

      fun new lambda = Lambda {lambda = lambda,
                               hash = newHash ()}

      fun hash (Lambda {hash, ...}) = hash

      fun dest (Lambda {lambda, ...}) = lambda

      fun equals (Lambda r, Lambda r') =
         #hash r = #hash r'
         andalso Sxml.Lambda.equals (#lambda r, #lambda r')

      fun layout (Lambda {lambda, ...}) =
         let open Layout
         in seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lambda)]
         end
   end

structure Lambdas = UniqueSet (structure Element = Lambda
                               val cacheSize: int = 5
                               val bits: int = 13)
in
structure LambdaNode:
   sig
      type t

      val addHandler: t * (Sxml.Lambda.t -> unit) -> unit
      val coerce: {from: t, to: t} -> unit
      val lambda: Sxml.Lambda.t -> t
      val layout: t -> Layout.t
      val new: unit -> t
      val toList: t -> Sxml.Lambda.t list
      val unify: t * t -> unit
   end =
   struct
      datatype t = LambdaNode of {me: Lambdas.t ref,
                                  handlers: (Lambda.t -> unit) list ref,
                                  coercedTo: t list ref} Dset.t

      fun toSet (LambdaNode d) = !(#me (Dset.! d))

      val layout = Lambdas.layout o toSet

      fun toList ln = List.map (Lambdas.toList (toSet ln), Lambda.dest)

      fun newSet s = LambdaNode (Dset.singleton {me = ref s,
                                                 handlers = ref [],
                                                 coercedTo = ref []})

      fun new () = newSet Lambdas.empty

      fun lambda l = newSet (Lambdas.singleton (Lambda.new l))

      fun handles (h: Lambda.t -> unit, s: Lambdas.t): unit =
         Lambdas.foreach (s, fn l => h l)

      fun handless (hs: (Lambda.t -> unit) list, s: Lambdas.t): unit =
         List.foreach (hs, fn h => handles (h, s))

      fun addHandler (LambdaNode d, h: Sxml.Lambda.t -> unit) =
         let val {me, handlers, ...} = Dset.! d
             val h = h o Lambda.dest
         in List.push (handlers, h)
            ; handles (h, !me)
         end

      fun send (LambdaNode d, s): unit =
         let val {me, coercedTo, handlers, ...} = Dset.! d
            val diff = Lambdas.- (s, !me)
         in if Lambdas.isEmpty diff
               then ()
            else (me := Lambdas.+ (diff, !me)
                  ; List.foreach (!coercedTo, fn to => send (to, diff))
                  ; handless (!handlers, diff))
         end

      val send =
         Trace.trace2
         ("AbstractValue.LambdaNode.send",
          layout, Lambdas.layout, Unit.layout)
         send

      fun equals (LambdaNode d, LambdaNode d') = Dset.equals (d, d')

      fun coerce {from = from as LambdaNode d, to: t}: unit =
         if equals (from, to)
            then ()
         else let
                 val {me, coercedTo, ...} = Dset.! d
              in
                 if List.exists (!coercedTo, fn ls => equals (ls, to))
                    then ()
                 else (List.push (coercedTo, to)
                       ; send (to, !me))
              end

      fun update (c, h, diff) =
         if Lambdas.isEmpty diff
            then ()
         else (List.foreach (c, fn to => send (to, diff))
               ; handless (h, diff))

      fun unify (LambdaNode d, LambdaNode d'): unit =
         if Dset.equals (d, d')
            then ()
         else
            let
               val {me = ref m, coercedTo = ref c, handlers = ref h, ...} =
                  Dset.! d
               val {me = ref m', coercedTo = ref c', handlers = ref h', ...} =
                  Dset.! d'
               val diff = Lambdas.- (m, m')
               val diff' = Lambdas.- (m', m)
            in Dset.union (d, d')
               ; (Dset.:=
                  (d, {me = ref (if Lambdas.isEmpty diff
                                   then m'
                                else Lambdas.+ (m', diff)),
                       coercedTo = ref (List.fold
                                        (c', c, fn (n', ac) =>
                                         if List.exists (c, fn n =>
                                                         equals (n, n'))
                                            then ac
                                         else n' :: ac)),
                       handlers = ref (List.appendRev (h, h'))}))
               ; update (c, h, diff')
               ; update (c', h', diff)
            end

(*
      val unify =
         Trace.trace2
         ("AbstractValue.LambdaNode.unify", layout, layout, Unit.layout)
         unify
*)
   end
end

structure UnaryTycon =
   struct
      datatype t = Array | Ref | Vector | Weak

      val toString =
         fn Array => "Array"
          | Ref => "Ref"
          | Vector => "Vector"
          | Weak => "Weak"

      val layout = Layout.str o toString
   end

datatype tree =
   Lambdas of LambdaNode.t
 | Tuple of t vector
 | Type of Type.t
 | Unify of UnaryTycon.t * t

withtype t = {tree: tree} Dset.t

fun new (tree: tree): t =
   Dset.singleton {tree = tree}

local
   fun make sel : t -> 'a = sel o Dset.!
in
   val tree = make #tree
end

fun layout v =
   let open Layout
   in case tree v of
      Type t => seq [str "Type ", Type.layout t]
    | Unify (t, v) => paren (seq [UnaryTycon.layout t, str " ", layout v])
    | Tuple vs => Vector.layout layout vs
    | Lambdas l => LambdaNode.layout l
   end

fun addHandler (v, h) =
   case tree v of
      Lambdas n => LambdaNode.addHandler (n, h)
    | _ => Error.bug "AbstractValue.addHandler: non-lambda"

local
   val {hom, destroy} =
      Type.makeMonoHom
      {con = fn (t, tycon, vs) =>
       let
       in if Tycon.equals (tycon, Tycon.arrow)
             then {isFirstOrder = false,
                   make = fn () => new (Lambdas (LambdaNode.new ()))}
          else
             if Vector.forall (vs, #isFirstOrder)
                then {isFirstOrder = true,
                      make = let val v = new (Type t)
                             in fn () => v
                             end}
             else
                {isFirstOrder = false,
                 make = let
                           fun mutable mt =
                              let val make = #make (Vector.sub (vs, 0))
                              in fn () => new (Unify (mt, make ()))
                              end
                        in if Tycon.equals (tycon, Tycon.reff)
                              then mutable UnaryTycon.Ref
                           else if Tycon.equals (tycon, Tycon.array)
                                   then mutable UnaryTycon.Array
                           else if Tycon.equals (tycon, Tycon.vector)
                                   then mutable UnaryTycon.Vector
                           else if Tycon.equals (tycon, Tycon.weak)
                                   then mutable UnaryTycon.Weak
                           else if Tycon.equals (tycon, Tycon.tuple)
                                   then (fn () =>
                                         new (Tuple
                                              (Vector.map (vs, fn {make, ...} =>
                                                           make ()))))
                           else Error.bug "AbstractValue.fromType: non-arrow"
                        end}
       end}
in
   val destroy = destroy
   val typeIsFirstOrder = #isFirstOrder o hom
   fun fromType t = #make (hom t) ()
end

val fromType = Trace.trace ("AbstractValue.fromType", Type.layout, layout) fromType

fun tuple (vs: t vector): t = new (Tuple vs)

fun lambda (l: Sxml.Lambda.t): t =
   new (Lambdas (LambdaNode.lambda l))

fun unify (v, v') =
   if Dset.equals (v, v')
      then ()
   else let val t = tree v
            val t' = tree v'
        in Dset.union (v, v')
           ; (case (t, t') of
                 (Type t, Type t') => if Type.equals (t, t')
                                         then ()
                                      else Error.bug "AbstractValue.unify: different types"
               | (Unify (_, v), Unify (_, v')) => unify (v, v')
               | (Tuple vs, Tuple vs') => Vector.foreach2 (vs, vs', unify)
               | (Lambdas l, Lambdas l') => LambdaNode.unify (l, l')
               | _ => Error.bug "AbstractValue.unify: different values")
        end

val unify = Trace.trace2 ("AbstractValue.unify", layout, layout, Unit.layout) unify

fun coerce {from: t, to: t}: unit =
   if Dset.equals (from, to)
      then ()
   else (case (tree from, tree to) of
            (Type t,    Type t')    => if Type.equals (t, t')
                                          then ()
                                       else Error.bug "coerce"
          | (Unify _, Unify _) =>
               (* Can't do a coercion for vectors, since that would imply
                * walking over the entire vector and coercing each element
                *)
               unify (from, to)
          | (Tuple vs,  Tuple vs')  =>
               Vector.foreach2 (vs, vs', fn (v, v') =>
                                coerce {from = v, to = v'})
          | (Lambdas l, Lambdas l') => LambdaNode.coerce {from = l, to = l'}
          | _ => Error.bug "AbstractValue.coerce: different values")

val coerce = Trace.trace ("AbstractValue.coerce",
                          fn {from, to} =>
                          let open Layout
                          in record [("from", layout from),
                                     ("to" , layout to)]
                          end, Unit.layout) coerce

structure Dest =
   struct
      datatype dest =
         Array of t
       | Lambdas of Sxml.Lambda.t list
       | Ref of t
       | Tuple of t vector
       | Type of Type.t
       | Vector of t
       | Weak of t
   end

fun dest v =
   case tree v of
      Type t => Dest.Type t
    | Unify (mt, v) => (case mt of
                           UnaryTycon.Array => Dest.Array v
                         | UnaryTycon.Ref => Dest.Ref v
                         | UnaryTycon.Vector => Dest.Vector v
                         | UnaryTycon.Weak => Dest.Weak v)
    | Tuple vs => Dest.Tuple vs
    | Lambdas l => Dest.Lambdas (LambdaNode.toList l)

open Dest

end
