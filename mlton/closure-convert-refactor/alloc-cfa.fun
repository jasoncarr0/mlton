functor AllocCFA(Alloc: ALLOCATOR): CFA =
struct

open Alloc

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

   structure LambdaFree = LambdaFree(Alloc)


   structure Proxy :>
   sig
      type t
      val all: unit -> t list
      val equals: t * t -> bool
      val layout: t -> Layout.t
      val new: unit -> t
      val plist: t -> PropertyList.t
   end =
   struct
      type t = Sxml.Var.t
      val all : t list ref = ref []
      val equals = Sxml.Var.equals
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
       | ConApp of (Sxml.Var.t * Addr.t) list * {con: Sxml.Con.t, arg: Sxml.Var.t option}
       | Lambda of (Sxml.Var.t * Addr.t) list * Sxml.Lambda.t * Sxml.Type.t
       | Ref of Proxy.t
       | Tuple of (Sxml.Var.t * Addr.t) vector
       | Vector of Proxy.t
       | Weak of Proxy.t

      fun equals (e, e') =
         case (e, e') of
            (Array p, Array p') => Proxy.equals (p, p')
          | (Base ty, Base ty') => Sxml.Type.equals (ty, ty')
          | (ConApp (_, {con = con, arg = arg}), ConApp (_, {con = con', arg = arg'})) =>
               Sxml.Con.equals (con, con') andalso
               Option.equals (arg, arg', Sxml.Var.equals)
          | (Lambda (_, lam, _), Lambda (_, lam', _)) =>
               Sxml.Lambda.equals (lam, lam')
          | (Ref p, Ref p') => Proxy.equals (p, p')
          | (Tuple xs, Tuple xs') =>
               Vector.equals (xs, xs', fn ((x1, a1), (x2, a2)) => 
                  Sxml.Var.equals (x1, x2) andalso Addr.equals (a1, a2))
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
             | ConApp (_, {con, arg}) => seq [Sxml.Con.layout con,
                                                 case arg of
                                                    NONE => empty
                                                  | SOME arg => seq [str " ",
                                                                     Sxml.Var.layout arg]]
             | Lambda (_, lam, _) => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam)]
             | Ref p => seq [str "Ref ", Proxy.layout p]
             | Tuple xs => seq [tuple (Vector.toListMap (xs, fn (x, _) => Sxml.Var.layout x))]
             | Vector p => seq [str "Vector ", Proxy.layout p]
             | Weak p => seq [str "Weak ", Proxy.layout p]
         end

      fun hash _ = 0wx0
   end
structure AbsVal = AbstractValue
structure AbstractValueSet = PowerSetLattice_ListSet(structure Element = AbstractValue)
structure AbsValSet = AbstractValueSet

fun cfa {config: Config.t} : t =
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
     
      val {get = addrInfo: Addr.t -> AbsValSet.t, 
           destroy = destroyAddrInfo} = 
           Addr.store {empty = fn _ => AbsValSet.empty ()}

      val {get = varAddrs: Sxml.Var.t -> Addr.t HashSet.t,
           destroy = destroyVarAddrs} =
         Property.destGet
         (Sxml.Var.plist,
          Property.initFun (fn _ => HashSet.new {hash=Addr.hash}))

      fun alloc (var, ctxt) = let
         val addr = Addr.alloc (var, ctxt)
      in
         HashSet.lookupOrInsert
         (varAddrs var, Addr.hash addr, 
          fn addr' => Addr.equals (addr, addr'),
          fn () => addr)
      end

      fun addrValue (var, ctxt) = 
         addrInfo (alloc (var, ctxt))

          


      val {get = proxyInfo: Proxy.t -> AbsValSet.t, ...} =
         Property.get
         (Proxy.plist,
          Property.initFun (fn _ => AbsValSet.empty ()))

      val {get = typeInfo: Sxml.Type.t -> AbsValSet.t,
           destroy = destroyTypeInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (AbsValSet.singleton o AbsVal.Base))

      val {get = lambdaInfo: Sxml.Lambda.t -> (Inst.t * AbsValSet.t) list ref,
           destroy = destroyLambdaInfo} =
         Property.destGet
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => ref []))

      val exnProxy = Proxy.new ()

      val {freeVars, freeRecVars, destroy = destroyLambdaFree} =
         LambdaFree.lambdaFree {program = program}
      fun compatibleLambda(ty: Sxml.Type.t, argTy: Sxml.Type.t, resTy: Sxml.Type.t) =
         (* we really need more machinery to check result types *)
            (* or go through the entire program *)
         Sxml.Type.equals(Sxml.Type.arrow(argTy, resTy), ty)
      (* List set is likely the best choice here since we can share some data *)
      (* Shadow when we have distinct addresses *)
      fun envGet (env, v1) = case List.peek (env, fn (v2, _) => Sxml.Var.equals(v1, v2)) of
            SOME (_, addr) => addr
          | NONE => Error.bug "envGet"
      val envValue = addrInfo o envGet
      fun envExpValue (env, v) = envValue (env, Sxml.VarExp.var v)
      type env = (Sxml.Var.t * Addr.t) list

      fun loopExp (ctxt: Inst.t, env, exp: Sxml.Exp.t): AbsValSet.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val resultVar = Sxml.VarExp.var result
            val (_, env') = List.fold (decs, (ctxt, env),
               fn (dec, (ctxt, env)) => loopDec (ctxt, env, dec))
         in
            envValue(env', resultVar)
         end
      and loopExp' (ctxt: Inst.t, env, exp: Sxml.Exp.t): unit = ignore (loopExp (ctxt, env, exp))
      and loopDec (ctxt: Inst.t, env, dec: Sxml.Dec.t): (Inst.t * env) =
         (case dec of
            Sxml.Dec.Fun {decs, ...} =>
               let
                  val env = Vector.fold(decs, env, fn ({var, ...}, env) =>
                     (var, alloc (var, ctxt)) :: env)
                  val nctxt = Vector.fold
                  (decs, ctxt, fn ({var, lambda, ty}, ctxt) => 
                  let
                     val addr = envGet (env, var)
                     val nctxt = Inst.preEval (ctxt, {var=var, exp=Sxml.PrimExp.Lambda lambda})
                     val _ = AbsValSet.<< (AbsVal.Lambda (env, lambda, ty), addrInfo addr)
                   in
                      (Inst.postBind (nctxt, {var=var, exp=Sxml.PrimExp.Lambda lambda}))
                   end)
               in
                  (nctxt, env)
               end
           | Sxml.Dec.MonoVal bind => loopBind (ctxt, env, bind)
           | _ => Error.bug "allocCFA.loopDec: strange dec")
      and loopBind (ctxt, env, bind as {var, exp, ...}): (Inst.t * env) = 
         let
            val addr = alloc (var, ctxt)
            val nctxt = Inst.preEval (ctxt, {var=var, exp=exp})
            val _ = AbsValSet.<= (loopPrimExp (nctxt, env, bind), addrValue(var, ctxt))
            val env' = (var, addr) :: env
         in
            (Inst.postBind (ctxt, {var=var, exp=exp}), env')
         end
      and loopPrimExp (ctxt, env, {exp: Sxml.PrimExp.t, ty: Sxml.Type.t, ...}): AbsValSet.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                           (envExpValue (env, func), fn v =>
                            case v of
                               AbsVal.Lambda (env', lambda', lamty) =>
                                  if not (
                                    (case Sxml.Type.deArrow lamty of 
                                        (_, res) => Sxml.Type.equals (res, ty) ))
                                        then ()
                                  else
                                  let
                                     val {arg = arg', body = body', ...} = Sxml.Lambda.dest lambda'
                                     
                                     val _ =
                                        Vector.foreach
                                        (freeVars lambda', fn x =>
                                         AbsValSet.<= (envValue (env', x),
                                                       addrValue(x, ctxt)))
                                     val _ =
                                        Vector.foreach
                                        (freeRecVars lambda', fn f =>
                                         AbsValSet.<= (envValue (env', f),
                                                       addrValue(f, ctxt)))
                                     val argAddr = alloc(arg', ctxt)
                                     val _ =
                                        AbsValSet.<=
                                        (envValue (env, (Sxml.VarExp.var arg)),
                                         addrInfo argAddr)

                                     val resVal =
                                        (case List.peek (!(lambdaInfo lambda'),
                                           fn (ctxt', _) => Inst.equals (ctxt, ctxt'))
                                        of
                                           SOME (_, v1) => v1
                                         | NONE =>
                                              let 
                                                 (* determinism ensures that all values that flow
                                                  * into res will flow into the other lambda
                                                  * and isolation of res ensures these are the
                                                  * only values *)
                                                 val _ = List.push (lambdaInfo lambda', (ctxt, res))
                                                 val v1 = loopExp (ctxt, (arg', argAddr)::env', body')
                                                 val _ = lambdaInfo lambda' := List.map (!(lambdaInfo lambda'),
                                                    fn (ctxt', x) => if Inst.equals (ctxt, ctxt')
                                                       then (ctxt', v1)
                                                    else (ctxt', x))
                                              in
                                                 v1
                                              end)
                                     val _ = AbsValSet.<= (resVal, res)
                                  in
                                     ()
                                  end
                             | _ => ())
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
                            val _ = AbsValSet.addHandler
                               (envExpValue (env, test), fn v =>
                                case v of
                                   AbsVal.ConApp (env', {con = con', arg = arg'}) =>
                                      (case Vector.peek (cases, fn (Sxml.Pat.T {con, ...}, _) =>
                                          Sxml.Con.equals (con, con')) of
                                          SOME (Sxml.Pat.T {arg, ...}, _) =>
                                             (case (arg', arg) of
                                                 (NONE, NONE) => ()
                                               | (SOME arg', SOME (arg, _)) =>
                                                    let
                                                       val _ = AbsValSet.<= 
                                                      (envValue (env', arg'), addrValue (arg, ctxt))
                                                    in
                                                       ()
                                                    end
                                               | _ => Error.bug "allocCFA.loopPrimExp: Case")
                                        | NONE => ())
                                 | _ => ())
                            val _ = Vector.foreach (cases, fn (Sxml.Pat.T {con, arg, ...}, exp) =>
                               let
                                  val _ = if Order.isFirstOrder (conOrder con)
                                   then Option.foreach (arg, fn (var, ty) =>
                                      AbsValSet.<= (typeInfo ty, addrValue(var, ctxt)))
                                   else ();
                                  val env' = case arg of 
                                      NONE => env
                                    | SOME (var, _) => (var, alloc(var, ctxt)) :: env
                               in
                                  AbsValSet.<= (loopExp (ctxt, env', exp), res)
                               end)
                         in
                            ()
                         end
                       | Sxml.Cases.Word _ => 
                            Sxml.Cases.foreach (cases, fn exp => 
                               AbsValSet.<= (loopExp (ctxt, env, exp), res))
                   val _ =
                      Option.foreach
                      (default, fn (exp, _) =>
                       AbsValSet.<= (loopExp (ctxt, env, exp), res))
                in
                   res
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                if Order.isFirstOrder (conOrder con)
                   then typeInfo ty
                   else AbsValSet.singleton (AbsVal.ConApp (env, {con = con, arg = Option.map (arg, Sxml.VarExp.var)}))
           | Sxml.PrimExp.Const _ =>
                typeInfo ty
           | Sxml.PrimExp.Handle {try, catch = (var, _), handler} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.<= (loopExp (ctxt, env, try), res)
                   val addr = alloc (var, ctxt)
                   val _ = AbsValSet.<= (proxyInfo exnProxy, addrInfo addr)
                   val _ = AbsValSet.<= (loopExp (ctxt, (var, addr) :: env, handler), res)
                in
                   res
                end
           | Sxml.PrimExp.Lambda lambda =>
                AbsValSet.singleton (AbsVal.Lambda (env, lambda, ty))
           | Sxml.PrimExp.PrimApp {prim, targs, args, ...} =>
                if Vector.forall (targs, fn ty => Order.isFirstOrder (typeOrder ty))
                   then typeInfo ty
                else
                let
                   val res = AbsValSet.empty ()
                   fun arg i = envExpValue (env, Vector.sub (args, i))
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
                              | _ => ())
                       | Array_update =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Array pa => AbsValSet.<= (arg 2, proxyInfo pa)
                               | _ => ());
                             AbsValSet.<= (typeInfo Sxml.Type.unit, res))
                       | Array_toVector =>
                            let
                               val pv = Proxy.new ()
                            in
                               AbsValSet.addHandler
                               (arg 0, fn v =>
                                case v of
                                   AbsVal.Array pa => AbsValSet.<= (proxyInfo pa, proxyInfo pv)
                                 | _ => ());
                               AbsValSet.<< (AbsVal.Vector pv, res)
                            end
                       | Ref_assign =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Ref pr => AbsValSet.<= (arg 1, proxyInfo pr)
                               | _ => ());
                             AbsValSet.<= (typeInfo Sxml.Type.unit, res))
                       | Ref_deref =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Ref pr => AbsValSet.<= (proxyInfo pr, res)
                              | _ => ())
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
                              | _ => ())
                       | Vector_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Vector pv => AbsValSet.<= (proxyInfo pv, res)
                              | _ => ())
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
                   val _ = AbsValSet.<= (envExpValue (env, exn), proxyInfo exnProxy)
                in
                   AbsValSet.empty ()
                end
           | Sxml.PrimExp.Select {tuple, offset} =>
                if Order.isFirstOrder (typeOrder ty)
                   then typeInfo ty
                   else let
                           val res = AbsValSet.empty ()
                           val _ = AbsValSet.addHandler
                                   (envExpValue (env, tuple), fn v =>
                                    case v of
                                       AbsVal.Tuple xs' =>
                                          AbsValSet.<= (addrInfo (#2 (Vector.sub (xs', offset))), res)
                                     | _ => ())
                        in
                           res
                        end
           | Sxml.PrimExp.Tuple xs =>
                if Order.isFirstOrder (typeOrder ty)
                   then typeInfo ty
                   else AbsValSet.singleton (AbsVal.Tuple (Vector.map (xs, 
                     fn v => (Sxml.VarExp.var v, envGet(env, Sxml.VarExp.var v)))))
           | Sxml.PrimExp.Var x =>
                envExpValue (env, x)
                )


      val _ = loopExp' (Inst.new config, [], body)

      val _ =
         Control.diagnostics
         (fn display =>
          (List.foreach
           (Proxy.all (), fn p =>
            (display o Layout.seq)
            [Proxy.layout p, Layout.str ": ", AbsValSet.layout (proxyInfo p)]);
           Sxml.Exp.foreachBoundVar
           (body, fn (x, _, _) =>
            List.foreach (HashSet.toList (varAddrs x), fn addr =>
            (display o Layout.seq)
            [Sxml.Var.layout x, Layout.str " @ ",
             Addr.layout addr, Layout.str " : ", 
             AbsValSet.layout (addrInfo addr)]))))

         

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, argTy, resTy, ...} =>
            List.removeDuplicates
            (List.concatMap (HashSet.toList (varAddrs func),
               fn s => 
                  List.keepAllMap(AbsValSet.getElements (addrInfo s), fn absVal =>
                     case absVal of 
                        AbsVal.Lambda (_, lam, ty) => if compatibleLambda(ty, argTy, resTy) 
                        then SOME lam
                        else NONE
                      | _ => NONE)),
             Sxml.Lambda.equals)
         
      val destroy = fn () =>
         (destroyConOrder ();
          destroyTyconOrder ();
          destroyTypeOrder ();
          destroyLambdaFree ();
          destroyAddrInfo ();
          destroyVarAddrs ();
          destroyTypeInfo ();
          destroyLambdaInfo ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "allocCFA")
   (cfa config)

local
   open Parse
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$
   fun mkCfg c = {config=c}
in
fun scan _ = cfa <$> mkCfg <$> (str "alloc(" *> Config.scan <* char #")")
end


end
