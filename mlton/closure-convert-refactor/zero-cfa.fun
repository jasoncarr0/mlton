(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


(* A basic 0CFA control-flow analysis, parameterized by the
 * implementation of abstract values.
*)
functor MkZeroCFA (S:
                   sig
                      include CFA_STRUCTS
                      structure AbstractValue :
                         sig
                            type t

                            datatype elt =
                               Array of t
                             | Base of Sxml.Type.t
                             | ConApp of {con: Sxml.Con.t, arg: t option}
                             | Lambda of Sxml.Lambda.t
                             | Ref of t
                             | Tuple of t vector
                             | Vector of t
                             | Weak of t
                            structure Elt :
                               sig
                                  type t = elt
                                  val layout: t -> Layout.t
                               end

                            val addHandler: t * (Sxml.Var.t -> t) * (elt -> unit) -> unit
                            val diagnostics: (Layout.t -> unit) -> unit
                            val flow: {from: t, to: t} -> unit
                            val forBool: t
                            val forUnit: t
                            val fromConApp: {con: Sxml.Con.t, arg: Sxml.Var.t option} * (Sxml.Var.t -> t) -> t
                            val fromLambda: Sxml.Lambda.t -> t
                            val fromTuple: Sxml.Var.t vector * (Sxml.Var.t -> t) -> t
                            val fromType: Sxml.Type.t -> t
                            val layout: t -> Layout.t
                            val new: unit -> t
                            val newArray: t -> t
                            val newRef: t -> t
                            val newVector: t -> t
                            val newWeak: t -> t
                         end
                   end) =
struct

open S
structure AbsVal = AbstractValue
structure AbsVal =
   struct
      open AbsVal
      val flow =
         Trace.trace
         ("AbsVal.flow",
          fn {from, to} =>
          Layout.record [("from", layout from), ("to", layout to)],
          Unit.layout)
         flow
   end

structure Config =
   struct
      datatype t = T of {firstOrderOpt: bool,
                         reachabilityExt: bool}
   end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

structure Order =
   struct
      structure L = TwoPointLattice (val bottom = "first-order"
                                     val top = "higher-order")
      open L
      val isFirstOrder = isBottom
      val makeHigherOrder = makeTop
   end


fun cfa {config: Config.t}: t =
   fn {program: Sxml.Program.t} =>
   let
      val Config.T {firstOrderOpt, reachabilityExt} = config
      val Sxml.Program.T {datatypes, body, ...} = program

      val {get = conOrder: Sxml.Con.t -> Order.t,
           rem = remConOrder} =
         Property.get
         (Sxml.Con.plist,
          Property.initFun (fn _ => Order.new ()))
      val destroyConOrder = fn () =>
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach (cons, remConOrder o #con))
      val {get = tyconOrder: Sxml.Tycon.t -> Order.t,
           rem = remTyconOrder} =
         Property.get
         (Sxml.Tycon.plist,
          Property.initFun (fn _ => Order.new ()))
      val destroyTyconOrder = fn () =>
         Vector.foreach
         (datatypes, remTyconOrder o #tycon)
      val {hom = typeOrder: Sxml.Type.t -> Order.t,
           destroy = destroyTypeOrder} =
         Sxml.Type.makeMonoHom
         {con = (fn (_, tycon, vs) =>
                 let
                    val res = Order.new ()
                    val _ =
                       if Sxml.Tycon.equals (tycon, Sxml.Tycon.arrow)
                          then Order.makeHigherOrder res
                       else (Order.<= (tyconOrder tycon, res);
                             Vector.foreach (vs, fn v => Order.<= (v, res)))
                 in
                    res
                 end)}
      val _ =
         Vector.foreach
         (datatypes, fn {tycon, cons, ...} =>
          Vector.foreach
          (cons, fn {con, arg} =>
           (Option.foreach (arg, fn ty =>
                            Order.<= (typeOrder ty, conOrder con));
            Order.<= (conOrder con, tyconOrder tycon))))


      val {get = varInfo: Sxml.Var.t -> {value: AbsVal.t},
           rem = remVarInfo} =
         Property.get
         (Sxml.Var.plist,
          Property.initFun (fn _ => {value = AbsVal.new ()}))
      fun destroyVarInfo () =
         Sxml.Exp.foreachBoundVar
         (body, fn (var, _, _) =>
          remVarInfo var)
      val varValue = #value o varInfo
      val varExpValue = varValue o Sxml.VarExp.var

      val {get = typeInfo: Sxml.Type.t -> {value: AbsVal.t},
           destroy = destroyTypeInfo} =
         if firstOrderOpt
            then Property.destGet
                 (Sxml.Type.plist,
                  Property.initFun (fn ty => {value = AbsVal.fromType ty}))
            else let
                    val {get = typeInfo,
                         set = setTypeInfo, destroy = destroyTypeInfo} =
                       Property.destGetSetOnce
                       (Sxml.Type.plist,
                        Property.initRaise ("ZeroCFA.tyInfo", Sxml.Type.layout))
                    val typeValue = #value o typeInfo

                    val _ = setTypeInfo (Sxml.Type.unit, {value = AbsVal.forUnit})
                    val _ = setTypeInfo (Sxml.Type.bool, {value = AbsVal.forBool})
                    fun setTypeInfoFromType ty =
                       setTypeInfo (ty, {value = AbsVal.fromType ty})
                    val _ = setTypeInfoFromType (Sxml.Type.cpointer)
                    val _ = setTypeInfoFromType (Sxml.Type.intInf)
                    val _ = Vector.foreach (Sxml.Tycon.reals, fn (_, rs) =>
                                            setTypeInfoFromType (Sxml.Type.real rs))
                    val _ = setTypeInfoFromType (Sxml.Type.thread)
                    val _ = Vector.foreach (Sxml.Tycon.words, fn (_, ws) =>
                                            setTypeInfoFromType (Sxml.Type.word ws))
                    val _ = Vector.foreach (Sxml.Tycon.words, fn (_, ws) =>
                                            let
                                               val ety = Sxml.Type.word ws
                                               val vty = Sxml.Type.vector ety
                                            in
                                               setTypeInfo (vty, {value = AbsVal.newVector (typeValue ety)})
                                            end)
                 in
                    {get = typeInfo, destroy = destroyTypeInfo}
                 end
      val typeValue = #value o typeInfo

      val {get = lambdaInfo: Sxml.Lambda.t -> bool,
           set = setLambdaInfo, destroy = destroyLambdaInfo} =
         Property.destGetSet
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => false))

      val exnAbsVal = AbsVal.new ()

      val traceLoopBind =
         Trace.trace
         ("ZeroCFA.loopBind",
          fn {var, ty = _: Sxml.Type.t, exp = _: Sxml.PrimExp.t} =>
          Layout.seq [Layout.str "val ", Sxml.Var.layout var],
          Unit.layout)

      fun loopExp (exp: Sxml.Exp.t): AbsVal.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val () = List.foreach (decs, loopDec)
         in
            varExpValue result
         end
      and loopExp' (exp: Sxml.Exp.t): unit = ignore (loopExp exp)
      and loopDec (dec: Sxml.Dec.t): unit =
         (case dec of
             Sxml.Dec.Fun {decs, ...} =>
                Vector.foreach
                (decs, fn {var, ty, lambda, ...} =>
                 loopBind {var = var, ty = ty,
                           exp = Sxml.PrimExp.Lambda lambda})
           | Sxml.Dec.MonoVal bind => loopBind bind
           | _ => Error.bug "ZeroCFA.loopDec: strange dec")
      and loopBind bind: unit =
         traceLoopBind
         (fn bind as {var, ...} =>
          AbsVal.flow {from = loopPrimExp bind,
                       to = varValue var})
         bind
      and loopPrimExp {ty: Sxml.Type.t, exp: Sxml.PrimExp.t, ...}: AbsVal.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val res = AbsVal.new ()
                   val _ = AbsVal.addHandler
                           (varExpValue func, varValue, fn v' =>
                            case v' of
                               AbsVal.Lambda lambda' =>
                                  let
                                     val {arg = arg', body = body', ...} = Sxml.Lambda.dest lambda'
                                  in
                                     AbsVal.flow {from = varExpValue arg,
                                                  to = varValue arg'};
                                     if reachabilityExt andalso not (lambdaInfo lambda')
                                        then (setLambdaInfo (lambda', true); loopExp' body')
                                        else ();
                                     AbsVal.flow {from = varExpValue (Sxml.Exp.result body'),
                                                  to = res}
                                  end
                             | _ => Error.bug "ZeroCFA.loopPrimExp: non-lambda")
                in
                   res
                end
           | Sxml.PrimExp.Case {test, cases, default} =>
                let
                   val res = AbsVal.new ()
                   val _ =
                      case cases of
                         Sxml.Cases.Con cases =>
                            let
                               val cases =
                                  Vector.map
                                  (cases, fn (Sxml.Pat.T {con, arg, ...}, _) =>
                                   {con = con, arg = arg})
                            in
                               if firstOrderOpt
                                  then AbsVal.addHandler
                                       (varExpValue test, varValue, fn v' =>
                                        case v' of
                                           AbsVal.ConApp {con = con', arg = arg'} =>
                                              (case Vector.peek (cases, fn {con, ...} =>
                                                                 Sxml.Con.equals (con, con')) of
                                                  SOME {arg = arg, ...} =>
                                                     (case (arg', arg) of
                                                         (NONE, NONE) => ()
                                                       | (SOME arg', SOME (arg, _)) =>
                                                            AbsVal.flow {from = arg',
                                                                         to = varValue arg}
                                                       | (NONE, SOME (arg, ty)) =>
                                                            AbsVal.flow  {from = typeValue ty,
                                                                          to = varValue arg}
                                                       | _ => Error.bug "ZeroCFA.loopPrimExp: Case")
                                                | NONE => ())
                                         | AbsVal.Base _ =>
                                              Vector.foreach
                                              (cases, fn {arg, ...} =>
                                               Option.foreach
                                               (arg, fn (arg, ty) =>
                                                AbsVal.flow {from = typeValue ty,
                                                             to = varValue arg}))
                                         | _ => Error.bug "ZeroCFA.loopPrimExp: non-con")
                                  else AbsVal.addHandler
                                       (varExpValue test, varValue, fn v' =>
                                        case v' of
                                           AbsVal.ConApp {con = con', arg = arg'} =>
                                              (case Vector.peek (cases, fn {con, ...} =>
                                                                 Sxml.Con.equals (con, con')) of
                                                  SOME {arg = arg, ...} =>
                                                     (case (arg', arg) of
                                                         (NONE, NONE) => ()
                                                       | (SOME arg', SOME (arg, _)) =>
                                                            AbsVal.flow {from = arg',
                                                                         to = varValue arg}
                                                       | _ => Error.bug "ZeroCFA.loopPrimExp: Case")
                                                | NONE => ())
                                         | _ => Error.bug "ZeroCFA.loopPrimExp: non-con")
                            end
                       | Sxml.Cases.Word _ => ()
                   val _ =
                      Sxml.Cases.foreach
                      (cases, fn exp =>
                       AbsVal.flow {from = loopExp exp, to = res})
                   val _ =
                      Option.foreach
                      (default, fn (exp, _) =>
                       AbsVal.flow {from = loopExp exp, to = res})
                in
                   res
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                let
                   fun mk arg =
                      AbsVal.fromConApp
                      ({con = con, arg = Option.map (arg, Sxml.VarExp.var)},
                       varValue)
                in
                   if firstOrderOpt
                      then if Order.isFirstOrder (typeOrder ty)
                              then typeValue ty
                              else if Order.isFirstOrder (conOrder con)
                                      then mk NONE
                                      else mk arg
                      else mk arg
                end
           | Sxml.PrimExp.Const c =>
                typeValue (Sxml.Type.ofConst c)
           | Sxml.PrimExp.Handle {try, catch = (var, _), handler} =>
                let
                   val res = AbsVal.new ()
                   val _ = AbsVal.flow {from = loopExp try, to = res}
                   val _ = AbsVal.flow {from = exnAbsVal, to = varValue var}
                   val _ = AbsVal.flow {from = loopExp handler, to = res}
                in
                   res
                end
           | Sxml.PrimExp.Lambda lambda =>
                (loopLambda lambda;
                 AbsVal.fromLambda lambda)
           | Sxml.PrimExp.PrimApp {prim, targs, args, ...} =>
                if firstOrderOpt andalso Vector.forall (targs, fn ty => Order.isFirstOrder (typeOrder ty))
                   then typeValue ty
                else
                let
                   fun arg i = varExpValue (Vector.sub (args, i))
                   fun bug (k, v) =
                      (Error.bug o String.concat)
                      ["ZeroCFA.loopPrimExp: non-", k,
                       " (got ", Layout.toString (AbsVal.Elt.layout v),
                       " for ", Sxml.Prim.Name.toString (Sxml.Prim.name prim), ")"]
                   datatype z = datatype Sxml.Prim.Name.t
                in
                   case Sxml.Prim.name prim of
                      Array_array =>
                         AbsVal.newArray (AbsVal.new ())
                    | Array_array0Const =>
                         AbsVal.newArray (AbsVal.new ())
                    | Array_sub =>
                         let
                            val res = AbsVal.new ()
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Array pa' => AbsVal.flow {from = pa', to = res}
                                 | _ => bug ("Array", v'))
                         in
                            res
                         end
                    | Array_update =>
                         let
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Array pa' => AbsVal.flow {from = arg 2, to = pa'}
                                 | _ => bug ("Array", v'))
                         in
                            typeValue Sxml.Type.unit
                         end
                    | Array_toVector =>
                         let
                            val pv = AbsVal.new ()
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Array pa' => AbsVal.flow {from = pa', to = pv}
                                 | _ => bug ("Array", v'))
                         in
                            AbsVal.newVector pv
                         end
                    | Ref_assign =>
                         let
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Ref pr' => AbsVal.flow {from = arg 1, to = pr'}
                                 | _ => bug ("Ref", v'))
                         in
                            typeValue Sxml.Type.unit
                         end
                    | Ref_deref =>
                         let
                            val res = AbsVal.new ()
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Ref pr' => AbsVal.flow {from = pr', to = res}
                                 | _ => bug ("Ref", v'))
                         in
                            res
                         end
                    | Ref_ref =>
                         AbsVal.newRef (arg 0)
                    | Weak_new =>
                         AbsVal.newWeak (arg 0)
                    | Weak_get =>
                         let
                            val res = AbsVal.new ()
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Weak pw' => AbsVal.flow {from = pw', to = res}
                                 | _ => bug ("Weak", v'))
                         in
                            res
                         end
                    | Vector_sub =>
                         let
                            val res = AbsVal.new ()
                            val _ =
                               AbsVal.addHandler
                               (arg 0, varValue, fn v' =>
                                case v' of
                                   AbsVal.Vector pv' => AbsVal.flow {from = pv', to = res}
                                 | _ => bug ("Vector", v'))
                         in
                            res
                         end
                    | _ =>
                         typeValue ty
                end
           | Sxml.PrimExp.Profile _ =>
                typeValue Sxml.Type.unit
           | Sxml.PrimExp.Raise {exn, ...} =>
                let
                   val _ = AbsVal.flow {from = varExpValue exn, to = exnAbsVal}
                in
                   AbsVal.new ()
                end
           | Sxml.PrimExp.Select {tuple, offset} =>
                if firstOrderOpt andalso Order.isFirstOrder (typeOrder ty)
                   then typeValue ty
                   else let
                           val res = AbsVal.new ()
                           val _ = AbsVal.addHandler
                                   (varExpValue tuple, varValue, fn v' =>
                                    case v' of
                                       AbsVal.Tuple xs' =>
                                          AbsVal.flow {from = Vector.sub (xs', offset), to = res}
                                     | _ => Error.bug "ZeroCFA.loopPrimExp: non-tuple")
                        in
                           res
                        end
           | Sxml.PrimExp.Tuple xs =>
                if firstOrderOpt andalso Order.isFirstOrder (typeOrder ty)
                   then typeValue ty
                   else AbsVal.fromTuple (Vector.map (xs, Sxml.VarExp.var), varValue)
           | Sxml.PrimExp.Var x =>
                varExpValue x)
      and loopLambda (lambda: Sxml.Lambda.t): unit =
         let
            val {body, ...} = Sxml.Lambda.dest lambda
            val _ =
               if reachabilityExt
                  then setLambdaInfo (lambda, false)
                  else loopExp' body
         in
            ()
         end

      val _ = loopExp' body

      val _ =
         Control.diagnostics
         (fn display =>
          (AbsVal.diagnostics display;
           Sxml.Exp.foreachBoundVar
           (body, fn (x, _, _) =>
            (display o Layout.seq)
            [Sxml.Var.layout x, Layout.str ": ", AbsVal.layout (varValue x)])))

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, ...} =>
         let
            val lams = ref []
            val _ =
               AbsVal.addHandler
               (varValue func, varValue, fn v =>
                case v of
                   AbsVal.Lambda lam => List.push (lams, lam)
                 | _ => Error.bug "ZeroCFA.cfa: non-lambda")
         in
            !lams
         end

      val destroy = fn () =>
         (destroyConOrder ();
          destroyTyconOrder ();
          destroyTypeOrder ();
          destroyVarInfo ();
          destroyTypeInfo ();
          destroyLambdaInfo ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "ZeroCFA")
   (cfa config)

end

functor MkZeroCFA_PSL (S:
                       sig
                          include CFA_STRUCTS
                          structure Proxy:
                             sig
                                type t
                                val all: unit -> t list
                                val equals: t * t -> bool
                                val hash: t -> Word.t
                                val layout: t -> Layout.t
                                val new: unit -> t
                                val plist: t -> PropertyList.t
                             end
                          structure Element:
                             sig
                                datatype t =
                                   Array of Proxy.t
                                 | Base of Sxml.Type.t
                                 | ConApp of {con: Sxml.Con.t, arg: Sxml.Var.t option}
                                 | Lambda of Sxml.Lambda.t
                                 | Ref of Proxy.t
                                 | Tuple of Sxml.Var.t vector
                                 | Vector of Proxy.t
                                 | Weak of Proxy.t
                                val equals: t * t -> bool
                                val layout: t -> Layout.t
                                val hash: t -> word
                                val unit: t
                                val truee: t
                                val falsee: t
                             end
                          structure ElementSet: POWERSET_LATTICE
                          sharing Element = ElementSet.Element
                       end) =
struct
open S
structure AbstractValue_PowerSetLattice =
   struct
      type t = ElementSet.t
      datatype elt =
         Array of t
       | Base of Sxml.Type.t
       | ConApp of {con: Sxml.Con.t, arg: t option}
       | Lambda of Sxml.Lambda.t
       | Ref of t
       | Tuple of t vector
       | Vector of t
       | Weak of t
      structure Elt =
         struct
            datatype t = datatype elt
            fun layout e =
               let
                  open Layout
               in
                  case e of
                     Array p => seq [str "Array ", ElementSet.layout p]
                   | Base ty => seq [str "Base ", Sxml.Type.layout ty]
                   | ConApp {con, arg} => seq [Sxml.Con.layout con,
                                               case arg of
                                                  NONE => empty
                                                | SOME arg => seq [str " ",
                                                                   ElementSet.layout arg]]
                   | Lambda lam => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam)]
                   | Ref p => seq [str "Ref ", ElementSet.layout p]
                   | Tuple xs => tuple (Vector.toListMap (xs, ElementSet.layout))
                   | Vector p => seq [str "Vector ", ElementSet.layout p]
                   | Weak p => seq [str "Weak ", ElementSet.layout p]
               end
         end

      val {get = proxyValue: Proxy.t -> ElementSet.t, ...} =
         Property.get
         (Proxy.plist,
          Property.initFun (fn _ => ElementSet.empty ()))

      fun addHandler (es, varValue, h) =
         ElementSet.addHandler
         (es, fn e =>
          case e of
             Element.Array pa => h (Elt.Array (proxyValue pa))
           | Element.Base ty => h (Elt.Base ty)
           | Element.ConApp {con, arg} => h (Elt.ConApp {con = con, arg = Option.map (arg, varValue)})
           | Element.Lambda lam => h (Elt.Lambda lam)
           | Element.Ref pr => h (Elt.Ref (proxyValue pr))
           | Element.Tuple xs => h (Elt.Tuple (Vector.map (xs, varValue)))
           | Element.Vector pv => h (Elt.Vector (proxyValue pv))
           | Element.Weak pw => h (Elt.Weak (proxyValue pw)))
      fun diagnostics display =
         List.foreach
         (Proxy.all (), fn p =>
          (display o Layout.seq)
          [Proxy.layout p, Layout.str ": ", ElementSet.layout (proxyValue p)])
      fun flow {from, to} = ElementSet.<= (from, to)
      val forBool = ElementSet.fromList [Element.truee, Element.falsee]
      val forUnit = ElementSet.singleton Element.unit
      fun fromConApp ({con, arg}, _) = ElementSet.singleton (Element.ConApp {con = con, arg = arg})
      fun fromLambda lam = ElementSet.singleton (Element.Lambda lam)
      fun fromTuple (xs, _) = ElementSet.singleton (Element.Tuple xs)
      fun fromType ty = ElementSet.singleton (Element.Base ty)
      val layout = ElementSet.layout
      val new = ElementSet.empty
      local
         fun mkNew mk es =
            let
               val p = Proxy.new ()
               val _ = ElementSet.<= (es, proxyValue p)
            in
               ElementSet.singleton (mk p)
            end
      in
         val newArray = mkNew Element.Array
         val newRef = mkNew Element.Ref
         val newVector = mkNew Element.Vector
         val newWeak = mkNew Element.Weak
      end
   end
structure ZeroCFA_PSL = MkZeroCFA(struct
                                     open S
                                     structure AbstractValue = AbstractValue_PowerSetLattice
                                  end)
open ZeroCFA_PSL
end

functor ZeroCFA (S: CFA_STRUCTS): CFA =
struct

open S

structure AbstractValueRep =
   struct
      datatype t = PowerSetLattice_ListSet | PowerSetLattice_UniqueSet
      fun scan charRdr strm =
         Scan.first [Scan.stringAs ("psl_ls", PowerSetLattice_ListSet),
                     Scan.stringAs ("psl_us", PowerSetLattice_UniqueSet)]
                    charRdr strm
   end
structure Config =
   struct
      datatype t = T of {abstractValueRep: AbstractValueRep.t,
                         firstOrderOpt: bool,
                         reachabilityExt: bool}
      val init = T {abstractValueRep = AbstractValueRep.PowerSetLattice_ListSet,
                    firstOrderOpt = true,
                    reachabilityExt = true}
      fun updateAbstractValueRep (T {firstOrderOpt, reachabilityExt, ...}: t, abstractValueRep) =
         T {abstractValueRep = abstractValueRep,
            firstOrderOpt = firstOrderOpt,
            reachabilityExt = reachabilityExt}
      fun updateFirstOrderOpt (T {abstractValueRep, reachabilityExt, ...}: t, firstOrderOpt) =
         T {abstractValueRep = abstractValueRep,
            firstOrderOpt = firstOrderOpt,
            reachabilityExt = reachabilityExt}
      fun updateReachabilityExt (T {abstractValueRep, firstOrderOpt, ...}: t, reachabilityExt) =
         T {abstractValueRep = abstractValueRep,
            firstOrderOpt = firstOrderOpt,
            reachabilityExt = reachabilityExt}
   end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

local
structure Proxy :>
   sig
      type t
      val all: unit -> t list
      val equals: t * t -> bool
      val hash: t -> Word.t
      val layout: t -> Layout.t
      val new: unit -> t
      val plist: t -> PropertyList.t
   end =
   struct
      type t = Sxml.Var.t
      val all : t list ref = ref []
      val equals = Sxml.Var.equals
      val hash = Sxml.Var.hash
      val layout = Sxml.Var.layout
      val new = fn () => let val p = Sxml.Var.newString "p"
                         in List.push (all, p); p
                         end
      val plist = Sxml.Var.plist
      val all = fn () => !all
   end
structure Element =
   struct
      datatype t =
         Array of Proxy.t
       | Base of Sxml.Type.t
       | ConApp of {con: Sxml.Con.t, arg: Sxml.Var.t option}
       | Lambda of Sxml.Lambda.t
       | Ref of Proxy.t
       | Tuple of Sxml.Var.t vector
       | Vector of Proxy.t
       | Weak of Proxy.t

      fun equals (e, e') =
         case (e, e') of
            (Array p, Array p') => Proxy.equals (p, p')
          | (Base ty, Base ty') => Sxml.Type.equals (ty, ty')
          | (ConApp {con = con, arg = arg}, ConApp {con = con', arg = arg'}) =>
               Sxml.Con.equals (con, con') andalso
               Option.equals (arg, arg', Sxml.Var.equals)
          | (Lambda lam, Lambda lam') => Sxml.Lambda.equals (lam, lam')
          | (Ref p, Ref p') => Proxy.equals (p, p')
          | (Tuple xs, Tuple xs') => Vector.equals (xs, xs', Sxml.Var.equals)
          | (Vector p, Vector p') => Proxy.equals (p, p')
          | (Weak p, Weak p') => Proxy.equals (p, p')
          | _ => false

      fun layout e =
         let
            open Layout
         in
            case e of
               Array p => seq [str "Array ", Proxy.layout p]
             | Base ty => seq [str "Base ", Sxml.Type.layout ty]
             | ConApp {con, arg} => seq [Sxml.Con.layout con,
                                         case arg of
                                            NONE => empty
                                          | SOME arg => seq [str " ",
                                                             Sxml.Var.layout arg]]
             | Lambda lam => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam)]
             | Ref p => seq [str "Ref ", Proxy.layout p]
             | Tuple xs => tuple (Vector.toListMap (xs, Sxml.Var.layout))
             | Vector p => seq [str "Vector ", Proxy.layout p]
             | Weak p => seq [str "Weak ", Proxy.layout p]
         end

      fun hash e =
         case e of
            Array p => Proxy.hash p
          | Base ty => Sxml.Type.hash ty
          | ConApp {con, arg} =>
               Option.fold
               (arg, Sxml.Con.hash con, fn (arg, hash) =>
                Word.xorb (Sxml.Var.hash arg, hash))
          | Lambda lam => Sxml.Var.hash (Sxml.Lambda.arg lam)
          | Ref p => Proxy.hash p
          | Tuple xs =>
               Vector.fold
               (xs, 0wx0, fn (x, hash) =>
                Word.xorb (Sxml.Var.hash x, hash))
          | Vector p => Proxy.hash p
          | Weak p => Proxy.hash p

      val unit = Tuple (Vector.new0 ())
      val truee = ConApp {con = Sxml.Con.truee, arg = NONE}
      val falsee = ConApp {con = Sxml.Con.falsee, arg = NONE}
   end
in
structure ZeroCFA_PSL_LS = MkZeroCFA_PSL(struct
                                            open S
                                            structure Proxy = Proxy
                                            structure Element = Element
                                            structure ElementSet =
                                               PowerSetLattice_ListSet(structure Element = Element)
                                         end)
structure ZeroCFA_PSL_US = MkZeroCFA_PSL(struct
                                            open S
                                            structure Proxy = Proxy
                                            structure Element = Element
                                            structure ElementSet =
                                               PowerSetLattice_UniqueSet(structure Element = Element)
                                         end)
end

fun cfa {config: Config.t}: t =
   let
      val Config.T {abstractValueRep, firstOrderOpt, reachabilityExt} = config
   in
      case abstractValueRep of
         AbstractValueRep.PowerSetLattice_ListSet =>
            let
               val config =
                  ZeroCFA_PSL_LS.Config.T
                  {firstOrderOpt = firstOrderOpt,
                   reachabilityExt = reachabilityExt}
            in
               ZeroCFA_PSL_LS.cfa {config = config}
            end
       | AbstractValueRep.PowerSetLattice_UniqueSet =>
            let
               val config =
                  ZeroCFA_PSL_US.Config.T
                  {firstOrderOpt = firstOrderOpt,
                   reachabilityExt = reachabilityExt}
            in
               ZeroCFA_PSL_US.cfa {config = config}
            end
   end

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
         (mkNameArgScan ("avr", AbstractValueRep.scan charRdr, Config.updateAbstractValueRep))::
         (mkNameArgScan ("fo", Bool.scan charRdr, Config.updateFirstOrderOpt))::
         (mkNameArgScan ("reach", Bool.scan charRdr, Config.updateReachabilityExt))::
         nil

      fun scanNameArgs (nameArgScans, config) strm =
         case nameArgScans of
            nameArgScan::nameArgScans =>
               (case nameArgScan config strm of
                   SOME (config', strm') =>
                      (case nameArgScans of
                          [] => (case charRdr strm' of
                                    SOME (#")", strm'') =>
                                       SOME (cfa {config = config'}, strm'')
                                  | _ => NONE)
                        | _ => (case charRdr strm' of
                                   SOME (#",", strm'') => scanNameArgs (nameArgScans, config') strm''
                                 | _ => NONE))
                 | _ => NONE)
          | _ => NONE
   in
      case Scan.string "0cfa" charRdr strm0 of
         SOME ((), strm1) =>
            (case charRdr strm1 of
                SOME (#"(", strm2) => scanNameArgs (nameArgScans, Config.init) strm2
              | _ => NONE)
       | _ => NONE
   end

end
