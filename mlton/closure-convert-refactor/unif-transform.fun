(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* A simple unification-based defunctionalization
 * transformation: use a unification-based flow analysis, informed by
 * the supplied control-flow analysis, to induce coercion-free
 * representations.
 *)
functor UnifTransform (S: TRANSFORM_STRUCTS): TRANSFORM =
struct

open S
open Sxml.Atoms

structure LambdaFree = LambdaFree(S)
structure Globalize = Globalize(S)

structure Config =
   struct
      datatype t = T of {globalizeOpt: bool, shrinkOpt: bool}
      val init = T {globalizeOpt = true, shrinkOpt = true}
      fun updateGlobalizeOpt (T {shrinkOpt, ...}: t, globalizeOpt) =
         T {globalizeOpt = globalizeOpt,
            shrinkOpt = shrinkOpt}
      fun updateShrinkOpt (T {globalizeOpt, ...}: t, shrinkOpt) =
         T {globalizeOpt = globalizeOpt,
            shrinkOpt = shrinkOpt}
   end

type t = {program: Sxml.Program.t,
          cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list} ->
         {program: Ssa.Program.t,
          destroy: unit -> unit}

structure AbstractValue =
struct

open S
open Sxml

structure Dset = DisjointSet

structure Lambda =
   struct
      open Lambda
      val hash = Var.hash o arg
      fun layout lambda =
         let open Layout
         in seq [str "fn ", Var.layout (arg lambda)]
         end
   end

structure Lambdas = UniqueSet (structure Element = Lambda
                               val cacheSize: int = 5
                               val bits: int = 13)
structure Lambdas =
   struct
      open Lambdas
      val size = List.length o toList
   end

structure LambdaNode:
   sig
      type t

      val lambda: Sxml.Lambda.t -> t
      val lambdas: Sxml.Lambda.t list -> t
      val layout: t -> Layout.t
      val new: unit -> t
      val toSet: t -> Lambdas.t
      val unify: t * t -> unit
   end =
   struct
      datatype t = LambdaNode of {set: Lambdas.t ref} Dset.t

      fun toSet (LambdaNode d) = !(#set (Dset.! d))

      val layout = Lambdas.layout o toSet

      fun newSet s = LambdaNode (Dset.singleton {set = ref s})

      fun new () = newSet Lambdas.empty

      fun lambda l = newSet (Lambdas.singleton l)

      fun lambdas ls = newSet (Lambdas.fromList ls)

      fun unify (LambdaNode d1, LambdaNode d2): unit =
         if Dset.equals (d1, d2)
            then ()
            else let
                    val {set = set1} = Dset.! d1
                    val {set = set2} = Dset.! d2
                    val _ = Dset.union (d1, d2)
                    val _ = Dset.:= (d1, {set = ref (Lambdas.+ (!set1, !set2))})
                 in
                    ()
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
 | Unary of UnaryTycon.t * t

withtype t = {tree: tree,
              cty: Ssa.Type.t option ref} Dset.t

fun new (tree: tree): t =
   Dset.singleton {tree = tree, cty = ref NONE}

local
   fun make sel : t -> 'a = sel o Dset.!
in
   val tree = make #tree
   val cty = make #cty
end

fun layout v =
   let open Layout
   in case tree v of
      Type t => seq [str "Type ", Type.layout t]
    | Unary (t, v) => paren (seq [UnaryTycon.layout t, str " ", layout v])
    | Tuple vs => Vector.layout layout vs
    | Lambdas l => LambdaNode.layout l
   end

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
                           fun unary mt =
                              let val make = #make (Vector.sub (vs, 0))
                              in fn () => new (Unary (mt, make ()))
                              end
                        in if Tycon.equals (tycon, Tycon.reff)
                              then unary UnaryTycon.Ref
                           else if Tycon.equals (tycon, Tycon.array)
                                   then unary UnaryTycon.Array
                           else if Tycon.equals (tycon, Tycon.vector)
                                   then unary UnaryTycon.Vector
                           else if Tycon.equals (tycon, Tycon.weak)
                                   then unary UnaryTycon.Weak
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

fun tuple (vs: t vector): t = new (Tuple vs)

fun lambda (l: Sxml.Lambda.t): t =
   new (Lambdas (LambdaNode.lambda l))

fun lambdas (ls: Sxml.Lambda.t list): t =
   new (Lambdas (LambdaNode.lambdas ls))

fun unify (v1, v2) =
   if Dset.equals (v1, v2)
      then ()
      else let
              val t1 = tree v1
              val t2 = tree v2
              val _ = Dset.union (v1, v2)
              val _ =
                 case (t1, t2) of
                    (Type t1, Type t2) => if Type.equals (t1, t2)
                                             then ()
                                             else Error.bug "AbstractValue.unify: different types"
                  | (Unary (_, v1), Unary (_, v2)) => unify (v1, v2)
                  | (Tuple vs1, Tuple vs2) => Vector.foreach2 (vs1, vs2, unify)
                  | (Lambdas l1, Lambdas l2) => LambdaNode.unify (l1, l2)
                  | _ => Error.bug "AbstractValue.unify: different values"
           in
              ()
           end

structure Dest =
   struct
      datatype dest =
         Array of t
       | Lambdas of Lambdas.t
       | Ref of t
       | Tuple of t vector
       | Type of Type.t
       | Vector of t
       | Weak of t
   end

fun dest v =
   case tree v of
      Type t => Dest.Type t
    | Unary (ut, v) => (case ut of
                           UnaryTycon.Array => Dest.Array v
                         | UnaryTycon.Ref => Dest.Ref v
                         | UnaryTycon.Vector => Dest.Vector v
                         | UnaryTycon.Weak => Dest.Weak v)
    | Tuple vs => Dest.Tuple vs
    | Lambdas ls => Dest.Lambdas (LambdaNode.toSet ls)

open Dest

end

structure AbsVal = AbstractValue

fun transform {config: Config.t}: t =
   fn {program: Sxml.Program.t, cfa} =>
   let
      val Config.T {globalizeOpt, shrinkOpt} = config
      val Sxml.Program.T {datatypes, body, overflow} = program
      val overflow = valOf overflow


      val {freeVars, freeRecVars, destroy = destroyLambdaFree, ...} =
         LambdaFree.lambdaFree {program = program}

      val {isGlobal, destroy = destroyGlobalize, ...} =
         if globalizeOpt
            then Globalize.globalize {program = program, freeVars = freeVars}
            else {isGlobal = fn _ => false, destroy = fn () => ()}


      val {get = conInfo: Con.t -> {argValue: AbsVal.t option},
           set = setConInfo, rem = remConInfo} =
         Property.getSetOnce
         (Con.plist,
          Property.initRaise ("UnifTransform.conInfo", Con.layout))
      fun destroyConInfo () =
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach (cons, remConInfo o #con))
      val conArgValue = #argValue o conInfo
      val _ =
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach
          (cons, fn {con, arg} =>
           setConInfo (con, {argValue = Option.map (arg, AbsVal.fromType)})))

      val {get = varInfo: Var.t -> {oty: Sxml.Type.t, value: AbsVal.t, cvar: Var.t ref},
           set = setVarInfo, rem = remVarInfo} =
         Property.getSetOnce
         (Var.plist,
          Property.initRaise ("UnifTransform.varInfo", Var.layout))
      fun destroyVarInfo () =
         Sxml.Exp.foreachBoundVar
         (body, fn (var, _, _) =>
          remVarInfo var)
      val varValue = #value o varInfo
      val varExpValue = varValue o Sxml.VarExp.var
      val _ =
         Sxml.Exp.foreachBoundVar
         (body, fn (x, _, ty) =>
          setVarInfo (x, {oty = ty, value = AbsVal.fromType ty, cvar = ref x}))

      val {get = lambdaInfo: Sxml.Lambda.t -> {envVars: Var.t vector,
                                               envTy: Ssa.Type.t option ref,
                                               func: Ssa.Func.t,
                                               mkCon: unit -> Con.t},
           set = setLambdaInfo, destroy = destroyLambdaInfo} =
         Property.destGetSetOnce
         (Sxml.Lambda.plist,
          Property.initRaise ("TyTransform.lambdaInfo", Sxml.Lambda.layout))

      fun loopExp (exp: Sxml.Exp.t): AbsVal.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val () = List.foreach (decs, loopDec)
         in
            varExpValue result
         end
      and loopDec (dec: Sxml.Dec.t): unit =
         (case dec of
             Sxml.Dec.Fun {decs, ...} =>
                Vector.foreach
                (decs, fn {var, ty, lambda, ...} =>
                 loopBind {var = var, ty = ty,
                           exp = Sxml.PrimExp.Lambda lambda})
           | Sxml.Dec.MonoVal bind => loopBind bind
           | _ => Error.bug "UnifTransform.loopDec: strange dec")
      and loopBind {var = res, ty = resTy, exp}: unit =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val func = Sxml.VarExp.var func
                   val funcValue = varValue func
                   val arg = Sxml.VarExp.var arg
                   val argTy = #oty (varInfo arg)
                   val argValue = varValue arg
                   val resValue = varValue res
                   val lambdas =
                      cfa {arg = arg,
                           argTy = argTy,
                           func = func,
                           res = res,
                           resTy = resTy}
                   val _ =
                      AbsVal.unify (AbsVal.lambdas lambdas, funcValue)
                   val _ =
                      List.foreach
                      (lambdas, fn lambda =>
                       (AbsVal.unify (argValue, varValue (Sxml.Lambda.arg lambda));
                        AbsVal.unify (varExpValue (Sxml.Exp.result (Sxml.Lambda.body lambda)), resValue)))
                in
                   ()
                end
           | Sxml.PrimExp.Case {cases, default, ...} =>
                let
                   val resValue = varValue res
                   val _ =
                      case cases of
                         Sxml.Cases.Con cases =>
                            Vector.foreach
                            (cases, fn (Sxml.Pat.T {con, arg, ...}, _) =>
                             case (conArgValue con, arg) of
                                (NONE, NONE) => ()
                              | (SOME v, SOME (x, _)) => AbsVal.unify (v, varValue x)
                              | _ => Error.bug "UnifTransform.loopBind: Case")
                       | _ => ()
                   val _ =
                      Sxml.Cases.foreach
                      (cases, fn e =>
                       AbsVal.unify (loopExp e, resValue))
                   val _ =
                      Option.foreach
                      (default, fn (e, _) =>
                       AbsVal.unify (loopExp e, resValue))
                in
                   ()
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                (case (arg, conArgValue con) of
                    (NONE, NONE) => ()
                  | (SOME x, SOME v) => AbsVal.unify (varExpValue x, v)
                  | _ => Error.bug "UnifTransform.loopBind: ConApp")
           | Sxml.PrimExp.Const _ => ()
           | Sxml.PrimExp.Handle {try, handler, ...} =>
                let
                   val resValue = varValue res
                   val _ = AbsVal.unify (loopExp try, resValue)
                   val _ = AbsVal.unify (loopExp handler, resValue)
                in
                   ()
                end
           | Sxml.PrimExp.Lambda lambda =>
                let
                   val f = Var.originalName res
                   val conString =
                      String.concat
                      [String.toUpper (String.prefix (f, 1)),
                       String.dropFirst f,
                       "Env"]
                   val envVars = Vector.keepAll (freeVars lambda, not o isGlobal)
                   val envTy = ref NONE
                   val func = Func.newString f
                   val mkCon = fn () => Con.newString conString
                   val _ =
                      setLambdaInfo (lambda, {envVars = envVars,
                                              envTy = envTy,
                                              func = func,
                                              mkCon = mkCon})
                   val _ = loopExp (Sxml.Lambda.body lambda)
                in
                   AbsVal.unify (AbsVal.lambda lambda, varValue res)
                end
           | Sxml.PrimExp.PrimApp {prim, targs, args, ...} =>
                if Vector.forall (targs, AbsVal.typeIsFirstOrder)
                   then ()
                else
                let
                   fun arg i = varExpValue (Vector.sub (args, i))
                   fun bug (k, v) =
                      (Error.bug o String.concat)
                      ["UnifTransform.loopPrimExp: non-", k,
                       " (got ", Layout.toString (AbsVal.layout v),
                       " for ", Prim.Name.toString (Prim.name prim), ")"]
                   datatype z = datatype Prim.Name.t
                in
                   case Sxml.Prim.name prim of
                      Array_sub =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Array x => AbsVal.unify (x, varValue res)
                           | _ => bug ("Array", (arg 0)))
                    | Array_update =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Array x => AbsVal.unify (arg 2, x)
                           | _ => bug ("Array", arg 0))
                    | Array_toVector =>
                         (case (AbsVal.dest (arg 0), AbsVal.dest (varValue res)) of
                             (AbsVal.Array x, AbsVal.Vector y) =>
                                AbsVal.unify (x, y)
                           | (AbsVal.Array _, _) => bug ("Vector", varValue res)
                           | _ => bug ("Array", arg 0))
                    | Ref_assign =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Ref x => AbsVal.unify (arg 1, x)
                           | _ => bug ("Ref", arg 0))
                    | Ref_deref =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Ref x => AbsVal.unify (x, varValue res)
                           | _ => bug ("Ref", arg 0))
                    | Ref_ref =>
                         (case AbsVal.dest (varValue res) of
                             AbsVal.Ref x => AbsVal.unify (arg 0, x)
                           | _ => bug ("Ref", varValue res))
                    | Weak_new =>
                         (case AbsVal.dest (varValue res) of
                             AbsVal.Weak x => AbsVal.unify (arg 0, x)
                           | _ => bug ("Weak", varValue res))
                    | Weak_get =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Weak x => AbsVal.unify (x, varValue res)
                           | _ => bug ("Weak", arg 0))
                    | Vector_sub =>
                         (case AbsVal.dest (arg 0) of
                             AbsVal.Vector x => AbsVal.unify (x, varValue res)
                           | _ => bug ("Vector", arg 0))
                    | _ => ()
                end
           | Sxml.PrimExp.Profile _ => ()
           | Sxml.PrimExp.Raise _ => ()
           | Sxml.PrimExp.Select {tuple, offset} =>
                if AbsVal.typeIsFirstOrder resTy
                   then ()
                   else (case AbsVal.dest (varExpValue tuple) of
                            AbsVal.Tuple vs => AbsVal.unify (Vector.sub (vs, offset), varValue res)
                          | _ => Error.bug "UnifTransform.loopPrimExp: Select, non-tuple")
           | Sxml.PrimExp.Tuple xs =>
                if AbsVal.typeIsFirstOrder resTy
                   then ()
                   else AbsVal.unify (AbsVal.tuple (Vector.map (xs, varExpValue)), varValue res)
           | Sxml.PrimExp.Var x =>
                AbsVal.unify (varExpValue x, varValue res))
      val _ =
         Control.trace (Control.Pass, "loopExp")
         loopExp body
(*
      val _ =
         Control.diagnostics
         (fn display =>
          Sxml.Exp.foreachBoundVar
          (body, fn (x, _, _) => display (let open Layout
                                          in seq [Var.layout x,
                                                  str ": ",
                                                  AbsVal.layout (varValue x)]
                                          end)))
*)

      val (convertType, destroyConvertType) =
         let
            val {get, set, destroy, ...} =
               Property.destGetSetOnce (Tycon.plist, Property.initConst NONE)

            fun nullary c v =
               if Vector.isEmpty v
                  then c
               else Error.bug "TyTransform.nullary: non-nullary tycon"

            fun unary make v =
               if 1 = Vector.length v
                  then make (Vector.sub (v, 0))
               else Error.bug "TyTransform.unary: non-unary tycon"

            val tycons =
               [(Tycon.array, unary Ssa.Type.array),
                (Tycon.cpointer, nullary Ssa.Type.cpointer),
                (Tycon.intInf, nullary Ssa.Type.intInf),
                (Tycon.reff, unary Ssa.Type.reff),
                (Tycon.thread, nullary Ssa.Type.thread),
                (Tycon.tuple, Ssa.Type.tuple),
                (Tycon.vector, unary Ssa.Type.vector),
                (Tycon.weak, unary Ssa.Type.weak)]
               @ Vector.toListMap (Tycon.reals, fn (t, s) => (t, nullary (Ssa.Type.real s)))
               @ Vector.toListMap (Tycon.words, fn (t, s) => (t, nullary (Ssa.Type.word s)))

            val _ = List.foreach (tycons, fn (tycon, f) => set (tycon, SOME f))

            val {hom = convertType, destroy = destroyConvertType} =
               Sxml.Type.makeMonoHom
               {con = fn (_, tycon, ts) =>
                if Tycon.equals (tycon, Tycon.arrow)
                   then Error.bug "UnifTransform.convertType: arrow type"
                   else case get tycon of
                           NONE => nullary (Ssa.Type.datatypee tycon) ts
                         | SOME f => f ts}
         in
            (convertType,
             fn () => (destroy (); destroyConvertType ()))
         end
      val {get = lambdasInfoOpt, ...} =
         Property.get (AbsVal.Lambdas.plist, Property.initFun (fn _ => ref NONE))
      val lambdaDatatypes = ref []
      fun valueType (v: AbsVal.t) : Ssa.Type.t =
         let
            val r = AbsVal.cty v
         in
            case !r of
               SOME cty => cty
             | NONE =>
                  let
                     val t =
                        case AbsVal.dest v of
                           AbsVal.Array v => Ssa.Type.array (valueType v)
                         | AbsVal.Lambdas ls => lambdasType ls
                         | AbsVal.Ref v => Ssa.Type.reff (valueType v)
                         | AbsVal.Type t => convertType t
                         | AbsVal.Tuple vs => Ssa.Type.tuple (Vector.map (vs, valueType))
                         | AbsVal.Vector v => Ssa.Type.vector (valueType v)
                         | AbsVal.Weak v => Ssa.Type.weak (valueType v)
                     val _ = r := SOME t
                  in
                     t
                  end
         end
      and lambdasType (ls: AbsVal.Lambdas.t): Ssa.Type.t =
         #ty (lambdasInfo ls)
      and lambdasInfo (ls: AbsVal.Lambdas.t) =
         let
            val r = lambdasInfoOpt ls
         in
            case !r of
               SOME info => info
             | NONE =>
                  let
                     val tycon = Tycon.newString "lambdas"
                     val cons =
                        Vector.fromListMap
                        (AbsVal.Lambdas.toList ls, fn lambda =>
                         {lambda = lambda,
                          con = #mkCon (lambdaInfo lambda) ()})
                     val ty = Ssa.Type.datatypee tycon
                     val info = {ty = ty, cons = cons}
                     val _ = r := SOME info
                     val cons =
                        Vector.map
                        (cons, fn {con, lambda} =>
                         {con = con,
                          args = Vector.new1 (lambdaEnvTy lambda)})
                     val _ =
                        List.push
                        (lambdaDatatypes,
                         Ssa.Datatype.T {tycon = tycon, cons = cons})
                  in
                     info
                  end
         end
      and lambdaEnvTy (lambda: Sxml.Lambda.t) =
         let
            val {envVars, envTy, ...} = lambdaInfo lambda
         in
            case !envTy of
               SOME ty => ty
             | NONE =>
                  let
                     val ty = Ssa.Type.tuple (Vector.map (envVars, varType))
                     val _ = envTy := SOME ty
                  in
                     ty
                  end
         end
      and varType x = valueType (varValue x)
      val varExpType = varType o Sxml.VarExp.var

      fun lambdaAt (lambda, var) =
         case AbsVal.dest (varValue var) of
            AbsVal.Lambdas lambdas =>
               let
                  val {ty, cons} = lambdasInfo lambdas
               in
                  case Vector.peek (cons, fn {lambda = lambda', ...} =>
                                    Sxml.Lambda.equals (lambda, lambda')) of
                     SOME {con, ...} => {con = con, ty = ty}
                   | _ => Error.bug "UnifTransform.lambdaConAt: not found"
               end
          | _ => Error.bug "UnifTransform.lambdaConAt: non-lambdas"


      fun newVar x =
         let
            val x' =
               if isGlobal x
                  then x
                  else Var.new x
            val _ =
               #cvar (varInfo x) := x'
         in
            x'
         end
      fun newScope (xs: Var.t vector, f: Var.t vector -> 'a): 'a =
         let
            val old = Vector.map (xs, ! o #cvar o varInfo)
            val new = Vector.map (xs, newVar)
            val res = f new
            val () = Vector.foreach2 (xs, old, fn (x, x') =>
                                      #cvar (varInfo x) := x')
         in
            res
         end


      fun convertConArg (arg, f) =
         case arg of
            NONE => Vector.new0 ()
          | SOME arg => Vector.new1 (f arg)


      val datatypes =
         Vector.map
         (datatypes, fn {tycon, cons, ...} =>
          Ssa.Datatype.T
          {tycon = tycon,
           cons = (Vector.map
                   (cons, fn {con, ...} =>
                    {con = con,
                     args = convertConArg (conArgValue con, valueType)}))})


      val globals = ref []
      val functions = ref []
      val raises: Ssa.Type.t vector option =
         Exn.withEscape
         (fn escape =>
          (Sxml.Exp.foreachPrimExp
           (body, fn (_, _, e) =>
            case e of
               Sxml.PrimExp.Handle {catch = (_, ty), ...} =>
                  escape (SOME (Vector.new1 (convertType ty)))
               | _ => ())
             ; NONE))
      val shrinkFunction =
         if shrinkOpt
            then Ssa.shrinkFunction {globals = Vector.new0 ()}
            else fn f => f
      fun addFunction {args, body, isMain, mayInline, name, resTy} =
         let
            val (start, blocks) =
               Ssa.DirectExp.linearize
               (body, if isMain then Ssa.Handler.Dead else Ssa.Handler.Caller)
            val f =
               shrinkFunction
               (Ssa.Function.new {args = args,
                                  blocks = Vector.fromList blocks,
                                  mayInline = mayInline,
                                  name = name,
                                  raises = if isMain then NONE else raises,
                                  returns = SOME (Vector.new1 resTy),
                                  start = start})
            val f =
               if isMain
                  then Ssa.Function.profile (f, SourceInfo.main)
                  else f
         in
            List.push (functions, f)
         end


      fun convertBoundVar (x: Var.t, _: Sxml.Type.t) =
         let
            val cx = newVar x
            val cty = varType x
         in
            (cx, cty)
         end

      fun convertVar (x: Var.t) =
         let val {cvar, ...} = varInfo x
         in Ssa.DirectExp.var (!cvar, varType x)
         end
      fun convertVars xs = Vector.map (xs, convertVar)
      val convertVarExp = convertVar o Sxml.VarExp.var
      fun convertVarExps xs = Vector.map (xs, convertVarExp)
      fun convertExp (exp: Sxml.Exp.t): Ssa.DirectExp.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
         in
            Ssa.DirectExp.lett {decs = List.concatMap (decs, convertDec),
                                body = convertVarExp result}
         end
      and convertDec (dec: Sxml.Dec.t): {var: Var.t, exp: Ssa.DirectExp.t} list =
         (case dec of
             Sxml.Dec.MonoVal {var, ty, exp} =>
                let
                   val (cvar, cty) = convertBoundVar (var, ty)
                   val cdecs =
                      [{var = cvar,
                        exp = convertPrimExp {var = var, oty = ty, cty = cty, exp = exp}}]
                in
                   if isGlobal var
                      then (List.push (globals, cdecs); [])
                      else cdecs
                end
           | Sxml.Dec.Fun {decs, ...} =>
                if Vector.isEmpty decs
                   then []
                   else let
                           val global = isGlobal (#var (Vector.sub (decs, 0)))
                           val {var = envVar, ty = envTy, exp = envExp} =
                              makeLambdaEnv (#lambda (Vector.sub (decs, 0)))
                           val env = Ssa.DirectExp.var (envVar, envTy)
                           val cdecs =
                              {var = envVar, exp = envExp} ::
                              (Vector.toListMap
                               (decs, fn {var, ty, lambda} =>
                                let
                                   val (cvar, _) = convertBoundVar (var, ty)
                                in
                                   {var = cvar,
                                    exp = makeLambdaClos {var = var, lambda = lambda, env = env}}
                                end))
                           val _ =
                              Vector.foreach
                              (decs, fn {lambda, ...} =>
                               convertLambda {lambda = lambda, recs = decs})
                        in
                           if global
                              then (List.push (globals, cdecs); [])
                              else cdecs
                        end
           | _ => Error.bug "TyTransform.convertDec: strange dec")
      and convertPrimExp {var: Var.t, oty: Sxml.Type.t, cty: Ssa.Type.t, exp: Sxml.PrimExp.t}: Ssa.DirectExp.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val func = Sxml.VarExp.var func
                   val funcLambdas =
                      case AbsVal.dest (varValue func) of
                         AbsVal.Lambdas ls => ls
                       | _ => Error.bug "UnifTransform.convertPrimExp: App, non-lambdas"
                   val arg = Sxml.VarExp.var arg
                   val argTy = #oty (varInfo arg)
                   val res = var
                   val resTy = oty
                   val cfaLambdas =
                      cfa {arg = arg,
                           argTy = argTy,
                           func = func,
                           res = res,
                           resTy = resTy}
                   val msg = String.concat
                             ["unsound cfa:: ",
                              (Layout.toString o Sxml.Dec.layout o Sxml.Dec.MonoVal)
                              {var = var, ty = resTy, exp = exp}]
                in
                   Ssa.DirectExp.casee
                   {test = convertVar func,
                    cases = (Ssa.DirectExp.Con
                             (Vector.fromListMap
                              (cfaLambdas, fn lambda =>
                               let
                                  val con = #con (lambdaAt (lambda, func))
                                  val envTy = lambdaEnvTy lambda
                                  val {func, ...} = lambdaInfo lambda
                                  val env = (Var.newString "env", envTy)
                               in
                                  {con = con,
                                   args = Vector.new1 env,
                                   body = (Ssa.DirectExp.call
                                           {func = func,
                                            args = Vector.new2 (Ssa.DirectExp.var env,
                                                                convertVar arg),
                                            ty = cty})}
                               end))),
                    default = if List.length cfaLambdas < AbsVal.Lambdas.size funcLambdas
                                 then SOME (Ssa.DirectExp.bug msg)
                                 else NONE,
                    ty = cty}
                end
           | Sxml.PrimExp.Case {test, cases, default} =>
                Ssa.DirectExp.casee
                {test = convertVarExp test,
                 cases = (case cases of
                             Sxml.Cases.Con cases =>
                                Ssa.DirectExp.Con
                                (Vector.map
                                 (cases, fn (Sxml.Pat.T {con, arg, ...}, e) =>
                                  {con = con,
                                   args = convertConArg (arg, convertBoundVar),
                                   body = convertExp e}))
                           | Sxml.Cases.Word (ws, cases) =>
                                Ssa.DirectExp.Word
                                (ws,
                                 Vector.map
                                 (cases, fn (w, e) =>
                                  (w, convertExp e)))),
                 default = Option.map (default, convertExp o #1),
                 ty = cty}
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                Ssa.DirectExp.conApp
                {con = con,
                 args = convertConArg (arg, convertVarExp),
                 ty = cty}
           | Sxml.PrimExp.Const c =>
                Ssa.DirectExp.const c
           | Sxml.PrimExp.Handle {try, catch, handler} =>
                Ssa.DirectExp.handlee
                {try = convertExp try,
                 catch = convertBoundVar catch,
                 handler = convertExp handler,
                 ty = cty}
           | Sxml.PrimExp.Lambda lambda =>
                let
                   val res = var
                   val _ = convertLambda {lambda = lambda, recs = Vector.new0 ()}
                   val {var, ty, exp} = makeLambdaEnv lambda
                in
                   Ssa.DirectExp.lett
                   {decs = [{var = var, exp = exp}],
                    body = makeLambdaClos {var = res,
                                           lambda = lambda,
                                           env = Ssa.DirectExp.var (var, ty)}}
                end
           | Sxml.PrimExp.PrimApp {prim, args, ...} =>
                let
                   val prim = Prim.map (prim, convertType)
                   val targs =
                      Prim.extractTargs
                      (prim,
                       {args = Vector.map (args, varExpType),
                        result = cty,
                        typeOps = {deArray = Ssa.Type.deArray,
                                   deArrow = fn _ => Error.bug "UnifTransform.convertPrimExp: deArrow",
                                   deRef = Ssa.Type.deRef,
                                   deVector = Ssa.Type.deVector,
                                   deWeak = Ssa.Type.deWeak}})
                   val args = convertVarExps args
                in
                   if Prim.mayOverflow prim
                      then Ssa.DirectExp.arith
                           {prim = prim,
                            args = args,
                            overflow = Ssa.DirectExp.raisee (convertVar overflow),
                            ty = cty}
                      else Ssa.DirectExp.primApp
                           {prim = prim,
                            targs = targs,
                            args = args,
                            ty = cty}
                end
           | Sxml.PrimExp.Profile pe =>
                Ssa.DirectExp.profile pe
           | Sxml.PrimExp.Raise {exn, ...} =>
                Ssa.DirectExp.raisee (convertVarExp exn)
           | Sxml.PrimExp.Select {offset, tuple} =>
                Ssa.DirectExp.select
                {offset = offset,
                 tuple = convertVarExp tuple,
                 ty = cty}
           | Sxml.PrimExp.Tuple xs =>
                Ssa.DirectExp.tuple
                {exps = convertVarExps xs,
                 ty = cty}
           | Sxml.PrimExp.Var x =>
                convertVarExp x)
      and makeLambdaClos {var, lambda, env} =
         let
            val {con, ty} = lambdaAt (lambda, var)
         in
            Ssa.DirectExp.conApp
            {con = con,
             args = Vector.new1 env,
             ty = ty}
         end
      and makeLambdaEnv lambda =
         let
            val {envVars, ...} = lambdaInfo lambda
            val envTy = lambdaEnvTy lambda
            val env = Var.newString "env"
         in
            {var = env,
             ty = envTy,
             exp = Ssa.DirectExp.tuple
                   {exps = convertVars envVars,
                    ty = envTy}}
         end
      and convertLambda {lambda, recs} =
         let
            val {arg, argType, body, mayInline, ...} = Sxml.Lambda.dest lambda
            val {envVars, func, ...} = lambdaInfo lambda
            val envTy = lambdaEnvTy lambda
            val freeRecVars = freeRecVars lambda
            val recs = Vector.keepAll (recs, fn {var, ...} =>
                                       not (isGlobal var)
                                       andalso
                                       Vector.contains (freeRecVars, var, Var.equals))
         in
            newScope
            (envVars, fn envVars =>
             newScope
             (Vector.map (recs, #var), fn recs' =>
              let
                 val env = Var.newString "env"
                 val args = Vector.new2 ((env, envTy), convertBoundVar (arg, argType))
                 val resTy = varType (Sxml.VarExp.var (Sxml.Exp.result body))
                 val body =
                    Ssa.DirectExp.lett
                    {decs = ((Vector.toList o Vector.map2)
                             (recs, recs', fn ({var, lambda, ...}, cvar) =>
                              {var = cvar,
                               exp = makeLambdaClos {var = var,
                                                     lambda = lambda,
                                                     env = Ssa.DirectExp.var (env, envTy)}})),
                     body = convertExp body}
                 val body =
                    Ssa.DirectExp.detupleBind
                    {tuple = env,
                     tupleTy = envTy,
                     components = envVars,
                     body = body}
              in
                 addFunction {args = args,
                              body = body,
                              isMain = false,
                              mayInline = mayInline,
                              name = func,
                              resTy = resTy}
              end))
         end

      val main = Ssa.Func.newString "main"
      val () =
         addFunction {args = Vector.new0 (),
                      body = convertExp body,
                      isMain = true,
                      mayInline = false,
                      name = main,
                      resTy = Ssa.Type.unit}
      val globals =
         let
            val (_, blocks) =
               Ssa.DirectExp.linearize
               (Ssa.DirectExp.lett
                {decs = List.concatRev (!globals),
                 body = Ssa.DirectExp.unit},
                Ssa.Handler.Dead)
            val globals =
               case blocks of
                  [Ssa.Block.T {statements, ...}] => statements
                | _ => Error.bug "UnifTransform.globals"
         in
            globals
         end
      val program =
         Ssa.Program.T {datatypes = Vector.concat [datatypes,
                                                   Vector.fromList (!lambdaDatatypes)],
                        globals = globals,
                        functions = !functions,
                        main = main}
   in
      {program = program,
       destroy = fn () => (destroyLambdaFree ();
                           destroyGlobalize ();
                           AbsVal.destroy ();
                           destroyConInfo ();
                           destroyVarInfo ();
                           destroyLambdaInfo ();
                           destroyConvertType ())}
   end
val transform = fn config =>
   Control.trace (Control.Pass, "UnifTransform")
   (transform config)

fun scan _ charRdr strm0 =
   let
      fun mkNameArgScan (name, scanArg, updateConfig) (config: Config.t) strm0 =
         case Scan.string (name ^ ":") charRdr strm0 of
            SOME ((), strm1) =>
               (case scanArg strm1 of
                   SOME (arg, strm2) =>
                      SOME (updateConfig (config, arg), strm2)
                 | _ => NONE)
          | _ => NONE
      val nameArgScans =
         (mkNameArgScan ("g", Bool.scan charRdr, Config.updateGlobalizeOpt))::
         (mkNameArgScan ("s", Bool.scan charRdr, Config.updateShrinkOpt))::
         nil

      fun scanNameArgs (nameArgScans, config) strm =
         case nameArgScans of
            nameArgScan::nameArgScans =>
               (case nameArgScan config strm of
                   SOME (config', strm') =>
                      (case nameArgScans of
                          [] => (case charRdr strm' of
                                    SOME (#")", strm'') =>
                                       SOME (transform {config = config'}, strm'')
                                  | _ => NONE)
                        | _ => (case charRdr strm' of
                                   SOME (#",", strm'') => scanNameArgs (nameArgScans, config') strm''
                                 | _ => NONE))
                 | _ => NONE)
          | _ => NONE
   in
      case Scan.string "uniftrans" charRdr strm0 of
         SOME ((), strm1) =>
            (case charRdr strm1 of
                SOME (#"(", strm2) => scanNameArgs (nameArgScans, Config.init) strm2
              | _ => NONE)
       | _ => NONE
   end

end
