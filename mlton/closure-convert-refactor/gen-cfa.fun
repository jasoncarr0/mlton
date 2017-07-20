functor GenCFA(S: GEN_CFA_STRUCTS) = 
struct

open S
open Alloc

structure Config = Config

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

   structure LambdaFree = LambdaFree(S)


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
structure AbstractValue =
   struct
      datatype t =
         Array of Proxy.t
       | Base of Sxml.Type.t
       | ConApp of Inst.t * {con: Sxml.Con.t, arg: Sxml.Var.t option}
       | Lambda of Inst.t * Sxml.Lambda.t
       | Ref of Proxy.t
       | Tuple of Inst.t * Sxml.Var.t vector
       | Vector of Proxy.t
       | Weak of Proxy.t

      fun equals (e, e') =
         case (e, e') of
            (Array p, Array p') => Proxy.equals (p, p')
          | (Base ty, Base ty') => Sxml.Type.equals (ty, ty')
          | (ConApp (inst, {con = con, arg = arg}), ConApp (inst', {con = con', arg = arg'})) =>
               Inst.equals (inst, inst') andalso
               Sxml.Con.equals (con, con') andalso
               Option.equals (arg, arg', Sxml.Var.equals)
          | (Lambda (inst, lam), Lambda (inst', lam')) =>
               Inst.equals (inst, inst') andalso
               Sxml.Lambda.equals (lam, lam')
          | (Ref p, Ref p') => Proxy.equals (p, p')
          | (Tuple (inst, xs), Tuple (inst', xs')) =>
               Inst.equals (inst, inst') andalso
               Vector.equals (xs, xs', Sxml.Var.equals)
          | (Vector p, Vector p') => Proxy.equals (p, p')
          | (Weak p, Weak p') => Proxy.equals (p, p')
          | _ => false

      fun layout (e) =
         let
            open Layout
         in
            case e of
               Array p => seq [str "Array ", Proxy.layout p]
             | Base ty => seq [str "Base ", Sxml.Type.layout ty]
             | ConApp (inst, {con, arg}) => seq [Sxml.Con.layout con,
                                                 case arg of
                                                    NONE => empty
                                                  | SOME arg => seq [str " ",
                                                                     Sxml.Var.layout arg],
                                                 str " @ ", Inst.layout inst]
             | Lambda (inst, lam) => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam),
                                          str " @ ", Inst.layout inst]
             | Ref p => seq [str "Ref ", Proxy.layout p]
             | Tuple (inst, xs) => seq [tuple (Vector.toListMap (xs, Sxml.Var.layout)),
                                        str " @ ", Inst.layout inst]
             | Vector p => seq [str "Vector ", Proxy.layout p]
             | Weak p => seq [str "Weak ", Proxy.layout p]
         end

      fun hash _ = 0wx0
   end
structure AbsVal = AbstractValue
structure AbstractValueSet = PowerSetLattice_ListSet(structure Element = AbstractValue)
structure AbsValSet = AbstractValueSet

fun cfa (config: Config.t)
   (*config:{alloc: Sxml.Var.t * Inst.t -> 'b,
                equals: Inst.t * Inst.t -> bool,
                new: unit -> Inst.t, 
                layout: Inst.t -> Layout.t,
                postBind: Inst.t * Sxml.Var.t -> Inst.t,
                preEval: Inst.t * Sxml.PrimExp.t -> Inst.t,
                store: {empty: 'b -> AbsValSet.t} ->
                   {get: 'b -> AbsValSet.t,
                    coalesce: Sxml.Var.t -> ('b * AbsValSet.t) list,
                    destroy: Sxml.Var.t -> unit}}}*) : t =
   fn {program: Sxml.Program.t} =>
   let
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
     
      val {get = varInfo: Addr.t -> AbsValSet.t, 
           coalesce = allVarInfo: Sxml.Var.t -> (Addr.t * AbsValSet.t) list,
           destroy = remVarInfo} = 
           Alloc.store {empty = fn _ => AbsValSet.empty ()}
      fun varValue (var, ctxt) = 
         varInfo (Alloc.alloc (var, ctxt))

      val {get = proxyInfo: Proxy.t -> AbsValSet.t, ...} =
         Property.get
         (Proxy.plist,
          Property.initFun (fn _ => AbsValSet.empty ()))

      val {get = typeInfo: Sxml.Type.t -> AbsValSet.t,
           destroy = destroyTypeInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (AbsValSet.singleton o AbsVal.Base))

      val {get = lambdaInfo: Sxml.Lambda.t -> Inst.t list ref,
           destroy = destroyLambdaInfo} =
         Property.destGet
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => ref []))

      val exnProxy = Proxy.new ()

      val {freeVars, freeRecVars, destroy = destroyLambdaFree} =
         LambdaFree.lambdaFree {program = program}
      fun varExpValue(ve, ctxt) = varValue (Sxml.VarExp.var ve, ctxt)
      fun loopExp (ctxt: Inst.t, exp: Sxml.Exp.t): AbsValSet.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val _ = List.fold (decs, ctxt, fn (dec, ctxt) => loopDec (ctxt, dec))
         in
            varExpValue(result, ctxt)
         end
      and loopExp' (ctxt: Inst.t, exp: Sxml.Exp.t): unit = ignore (loopExp (ctxt, exp))
      and loopDec (ctxt: Inst.t, dec: Sxml.Dec.t): Inst.t =
         (case dec of
            Sxml.Dec.Fun {decs, ...} =>
               Vector.fold
               (decs, ctxt, fn ({var, lambda, ...}, ctxt) => 
               let
                  val _ = AbsValSet.<< (AbsVal.Lambda (ctxt, lambda), varValue(var, ctxt)) 
                in
                   Alloc.postBind (ctxt, var)
                end)
           | Sxml.Dec.MonoVal bind => loopBind (ctxt, bind)
           | _ => Error.bug "mCFA.loopDec: strange dec")
      and loopBind (ctxt, bind as {var, ...}): Inst.t = 
         let
            val _ = AbsValSet.<= (loopPrimExp (ctxt, bind), varValue(var, ctxt))
         in
            Alloc.postBind (ctxt, var)
         end
      and loopPrimExp (ctxt, {var: Sxml.Var.t, ty: Sxml.Type.t, exp: Sxml.PrimExp.t, ...}): AbsValSet.t =
         let
            val nctxt = Alloc.preEval (ctxt, exp)
         in
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                           (varExpValue(func, ctxt), fn v =>
                            case v of
                               AbsVal.Lambda (ctxt', lambda') =>
                                  let
                                     val {arg = arg', body = body', ...} = Sxml.Lambda.dest lambda'

                                     val _ =
                                        Vector.foreach
                                        (freeVars lambda', fn x =>
                                         AbsValSet.<= (varValue (x, ctxt'),
                                                       varValue(x, nctxt)))
                                     val _ =
                                        Vector.foreach
                                        (freeRecVars lambda', fn f =>
                                         AbsValSet.<= (varValue(f, ctxt'),
                                                       varValue(f, nctxt)))
val _ =
                                        AbsValSet.<=
                                        (varExpValue(arg, ctxt),
                                         varValue(arg', nctxt))

                                     val _ =
                                        if List.contains (!(lambdaInfo lambda'), nctxt, Inst.equals)
                                           then ()
                                           else (List.push (lambdaInfo lambda', nctxt);
                                                 loopExp' (nctxt, body'))

                                     val _ =
                                        AbsValSet.<=
                                        (varExpValue (Sxml.Exp.result body', nctxt),
                                         res)
                                  in
                                     ()
                                  end
                             | _ => Error.bug "mCFA.loopPrimExp: non-lambda")
                in
                   res
                end
           | Sxml.PrimExp.Case {test, cases, default} =>
                let
                   val res = AbsValSet.empty ()
                   val _ =
                      case cases of
                         Sxml.Cases.Con cases =>
                            let
                               val cases =
                                  Vector.map
                                  (cases, fn (Sxml.Pat.T {con, arg, ...}, _) =>
                                   {con = con, arg = arg})
                            in
                               Vector.foreach
                               (cases, fn {con, arg} =>
                                if Order.isFirstOrder (conOrder con)
                                   then Option.foreach (arg, fn (arg, ty) =>
                                      AbsValSet.<= (typeInfo ty, varValue(arg, ctxt)))
                                   else ());
                               AbsValSet.addHandler
                               (varExpValue(test, ctxt), fn v =>
                                case v of
                                   AbsVal.ConApp (ctxt', {con = con', arg = arg'}) =>
                                      (case Vector.peek (cases, fn {con, ...} =>
                                          Sxml.Con.equals (con, con')) of
                                          SOME {arg, ...} =>
                                             (case (arg', arg) of
                                                 (NONE, NONE) => ()
                                               | (SOME arg', SOME (arg, _)) =>
                                                    AbsValSet.<= 
                                                      (varValue(arg', ctxt'), varValue(arg, ctxt))
                                               | _ => Error.bug "mCFA.loopPrimExp: Case")
                                        | NONE => ())
                                 | AbsVal.Base _ => ()
                                 | _ => Error.bug "mCFA.loopPrimExp: non-con")
                            end
                       | Sxml.Cases.Word _ => ()
                   val _ =
                      Sxml.Cases.foreach
                      (cases, fn exp =>
                       AbsValSet.<= (loopExp (ctxt, exp), res))
                   val _ =
                      Option.foreach
                      (default, fn (exp, _) =>
                       AbsValSet.<= (loopExp (ctxt, exp), res))
                in
                   res
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                if Order.isFirstOrder (conOrder con)
                   then typeInfo ty
                   else AbsValSet.singleton (AbsVal.ConApp (ctxt, {con = con, arg = Option.map (arg, Sxml.VarExp.var)}))
           | Sxml.PrimExp.Const c =>
                typeInfo ty
           | Sxml.PrimExp.Handle {try, catch = (var, _), handler} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.<= (loopExp (ctxt, try), res)
                   val _ = AbsValSet.<= (proxyInfo exnProxy, varValue(var, ctxt))
                   val _ = AbsValSet.<= (loopExp (ctxt, handler), res)
                in
                   res
                end
           | Sxml.PrimExp.Lambda lambda =>
                AbsValSet.singleton (AbsVal.Lambda (ctxt, lambda))
           | Sxml.PrimExp.PrimApp {prim, targs, args, ...} =>
                if Vector.forall (targs, fn ty => Order.isFirstOrder (typeOrder ty))
                   then typeInfo ty
                else
                let
                   val res = AbsValSet.empty ()
                   fun arg i = varExpValue (Vector.sub (args, i), ctxt)
                   fun bug (k, v) =
                      (Error.bug o String.concat)
                      ["mCFA.loopPrimExp: non-", k,
                       " (got ", Layout.toString (AbsVal.layout v),
                       " for ",Sxml.Prim.Name.toString (Sxml.Prim.name prim), ")"]
                   datatype z = datatype Sxml.Prim.Name.t
                   val _ =
                      case Sxml.Prim.name prim of
                         Array_uninit =>
                            let
                               val pa = Proxy.new ()
                            in
                               AbsValSet.<< (AbsVal.Array pa, res)
                            end
                       | Array_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Array pa => AbsValSet.<= (proxyInfo pa, res)
                              | _ => bug ("Array", v))
                       | Array_update =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Array pa => AbsValSet.<= (arg 2, proxyInfo pa)
                               | _ => bug ("Array", v));
                             AbsValSet.<= (typeInfo Sxml.Type.unit, res))
                       | Array_toVector =>
                            let
                               val pv = Proxy.new ()
                            in
                               AbsValSet.addHandler
                               (arg 0, fn v =>
                                case v of
                                   AbsVal.Array pa => AbsValSet.<= (proxyInfo pa, proxyInfo pv)
                                 | _ => bug ("Array", v));
                               AbsValSet.<< (AbsVal.Vector pv, res)
                            end
                       | Ref_assign =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Ref pr => AbsValSet.<= (arg 1, proxyInfo pr)
                               | _ => bug ("Ref", v));
                             AbsValSet.<= (typeInfo Sxml.Type.unit, res))
                       | Ref_deref =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Ref pr => AbsValSet.<= (proxyInfo pr, res)
                              | _ => bug ("Ref", v))
                       | Ref_ref =>
                            let
                               val pr = Proxy.new ()
                            in
                               AbsValSet.<= (arg 0, proxyInfo pr);
                               AbsValSet.<< (AbsVal.Ref pr, res)
                            end
                       | Weak_new =>
                            let
                               val pw = Proxy.new ()
                            in
                               AbsValSet.<= (arg 0, proxyInfo pw);
                               AbsValSet.<< (AbsVal.Weak pw, res)
                            end
                       | Weak_get =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Weak pw => AbsValSet.<= (proxyInfo pw, res)
                              | _ => bug ("Weak", v))
                       | Vector_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Vector pv => AbsValSet.<= (proxyInfo pv, res)
                              | _ => bug ("Vector", v))
                       | Vector_vector =>
                            let
                               val pa = Proxy.new ()
                            in
                               AbsValSet.<< (AbsVal.Vector pa, res)
                            end
                       
                       | _ =>
                            AbsValSet.<= (typeInfo ty, res)
                in
                   res
                end
           | Sxml.PrimExp.Profile _ =>
                typeInfo ty
           | Sxml.PrimExp.Raise {exn, ...} =>
                let
                   val _ = AbsValSet.<= (varExpValue(exn, ctxt), proxyInfo exnProxy)
                in
                   AbsValSet.empty ()
                end
           | Sxml.PrimExp.Select {tuple, offset} =>
                if Order.isFirstOrder (typeOrder ty)
                   then typeInfo ty
                   else let
                           val res = AbsValSet.empty ()
                           val _ = AbsValSet.addHandler
                                   (varExpValue(tuple, ctxt), fn v =>
                                    case v of
                                       AbsVal.Tuple (ctxt', xs') =>
                                          AbsValSet.<= (varValue (Vector.sub (xs', offset), ctxt'), res)
                                     | _ => Error.bug "mCFA.loopPrimExp: non-tuple")
                        in
                           res
                        end
           | Sxml.PrimExp.Tuple xs =>
                if Order.isFirstOrder (typeOrder ty)
                   then typeInfo ty
                   else AbsValSet.singleton (AbsVal.Tuple (ctxt, Vector.map (xs, Sxml.VarExp.var)))
           | Sxml.PrimExp.Var x =>
                varExpValue(x, ctxt))
         end


      val _ = loopExp' (Alloc.new config, body)

      val _ =
         Control.diagnostics
         (fn display =>
          (List.foreach
           (Proxy.all (), fn p =>
            (display o Layout.seq)
            [Proxy.layout p, Layout.str ": ", AbsValSet.layout (proxyInfo p)]);
           Sxml.Exp.foreachBoundVar
           (body, fn (x, _, _) =>
           display (Layout.str "Not implemented")
            (*List.foreach (!(varInfo x), fn (ctxt, v) =>
            (display o Layout.seq)
            [Sxml.Var.layout x, Layout.str " @ ",
             Config.layout ctxt, Layout.str " : ", 
             AbsValSet.layout(v, (Config.layout))])*))))

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, ...} =>
            List.concatMap (allVarInfo func, 
               fn (_, s) => 
                  List.keepAllMap(AbsValSet.getElements s, fn absVal =>
                     case absVal of 
                        AbsVal.Lambda (_, lam) => SOME lam
                      | _ => NONE))
         
      val destroy = fn () =>
         (destroyConOrder ();
          destroyTyconOrder ();
          destroyTypeOrder ();
          destroyLambdaFree ();
          Sxml.Exp.foreachBoundVar
          (body, fn (var, _, _) =>
           remVarInfo var);
          destroyTypeInfo ();
          destroyLambdaInfo ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "genCFA")
   (cfa config)

fun scan _ charRdr strm0 =
   let
      fun mkNameArgScan (name, scanArg, updateConfig) (config: Config.t) strm0 =
         case Scan.string (name ^ ":") charRdr strm0 of
            SOME ((), strm1) =>
               (case scanArg strm1 of
                   SOME (arg, strm2) =>
                      SOME (updateConfig arg, strm2)
                 | _ => NONE)
          | _ => NONE
      val nameArgScans =
         (mkNameArgScan ("m", Int.scan (StringCvt.DEC, charRdr), Config.fromN))::
         nil

      fun scanNameArgs (nameArgScans, config) strm =
         case nameArgScans of
            nameArgScan::nameArgScans =>
               (case nameArgScan config strm of
                   SOME (config', strm') =>
                      (case nameArgScans of
                          [] => (case charRdr strm' of
                                    SOME (#")", strm'') => SOME (cfa config', strm'')
                                  | _ => NONE)
                        | _ => (case charRdr strm' of
                                   SOME (#",", strm'') => scanNameArgs (nameArgScans, config') strm''
                                 | _ => NONE))
                 | _ => NONE)
          | _ => NONE
   in
      case Scan.string "gencfa" charRdr strm0 of
         SOME ((), strm1) =>
            (case charRdr strm1 of
                SOME (#"(", strm2) => scanNameArgs (nameArgScans, Config.fromN 0) strm2
              | _ => NONE)
       | _ => NONE
   end

(*
local
   structure T = StreamParser
   open T.Ops
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$
in
fun scan _ charRdr strm0 = T.parse (T.optional (cfa <$> (
      T.string "gencfa(" *>
      (T.any 
         [mAlloc <$> (T.string "m:" *> String.implode <$> T.many(T.sat(T.next, Char.isDigit)))])
      <* T.char #")"
   )), raise Fail "") handle Fail _ => NONE
  (* 
   case Scan.string "alloccfa" charRdr strm0 of
      SOME ((), strm1) => SOME (cfa {alloc = raise Fail ""}, strm1)
    | _ => NONE*)
end
   *)


end
