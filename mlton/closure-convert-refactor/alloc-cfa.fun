(* Copyright (C) 2017 Jason Carr.
 * Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* A generic CFA that uses an allocator to decide its behaviour
 *)
functor AllocCFA(Allocator: ALLOCATOR): CFA =
struct

open Allocator
structure Allocator = Allocator

type t = {program: Sxml.Program.t} ->
           {canRaise: Sxml.Lambda.t -> bool,
            caseUsed: {res: Sxml.Var.t,
                       con: Sxml.Con.t} ->
               bool,
            cfa: {arg: Sxml.Var.t,
                  argTy: Sxml.Type.t,
                  func: Sxml.Var.t,
                  res: Sxml.Var.t,
                  resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
            destroy: unit -> unit,
            knownCon: {res: Sxml.Var.t} ->
               {arg: Sxml.VarExp.t option,
                con: Sxml.Con.t} option,
            varUsed: {var: Sxml.Var.t} ->
               bool}


   structure LambdaFree = LambdaFree(Allocator)


structure AbstractValue =
   struct
      datatype t =
         Array of Addr.t
       | Base of Sxml.Type.t
       | ConApp of {con: Sxml.Con.t, arg: (Sxml.Var.t * Addr.t) option}
       | Lambda of (Sxml.Var.t * Addr.t) vector * Sxml.Lambda.t * Sxml.Type.t
       | Ref of Addr.t
       | Tuple of (Sxml.Var.t * Addr.t) vector
       | Vector of Addr.t
       | Weak of Addr.t

      fun equals (e, e') =
         case (e, e') of
            (Array p, Array p') => Addr.equals (p, p')
          | (Base ty, Base ty') => Sxml.Type.equals (ty, ty')
          | (ConApp {con = con, arg = arg}, ConApp {con = con', arg = arg'}) =>
               Sxml.Con.equals (con, con') andalso
               Option.equals (arg, arg', fn ((var, addr), (var', addr')) =>
               Sxml.Var.equals (var, var') andalso
               Addr.equals (addr, addr'))
          | (Lambda (env, lam, _), Lambda (env', lam', _)) =>
               Vector.equals (env, env', fn ((var, addr), (var', addr')) =>
                  Sxml.Var.equals (var, var') andalso
                  Addr.equals (addr, addr')) andalso
               Sxml.Lambda.equals (lam, lam')
          | (Ref p, Ref p') => Addr.equals (p, p')
          | (Tuple xs, Tuple xs') =>
               Vector.equals (xs, xs', fn ((x1, a1), (x2, a2)) => 
                  Sxml.Var.equals (x1, x2) andalso Addr.equals (a1, a2))
          | (Vector p, Vector p') => Addr.equals (p, p')
          | (Weak p, Weak p') => Addr.equals (p, p')
          | _ => false

      fun layout (e) =
         let
            open Layout
         in
            case e of
               Array p => seq [str "Array ", Addr.layout p]
             | Base ty => seq [str "Base ", Sxml.Type.layout ty]
             | ConApp {con, arg} => seq [Sxml.Con.layout con,
                                                 case arg of
                                                    NONE => empty
                                                  | SOME (arg, addr) => seq
                                                      [str " ",
                                                       Sxml.Var.layout arg,
                                                       str " [",
                                                       Addr.layout addr,
                                                       str "]"]]
             | Lambda (_, lam, _) => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam)]
             | Ref p => seq [str "Ref ", Addr.layout p]
             | Tuple xs => seq [tuple (Vector.toListMap (xs, fn (_, a) => Addr.layout a))]
             | Vector p => seq [str "Vector ", Addr.layout p]
             | Weak p => seq [str "Weak ", Addr.layout p]
         end

      fun hash _ = 0wx0
   end
structure AbsVal = AbstractValue
structure AbstractValueSet = PowerSetLattice_ListSet(structure Element = AbstractValue)
structure AbsValSet = AbstractValueSet

fun cfa {config: Config.t} : t =
   fn {program: Sxml.Program.t} =>
   let
      val Sxml.Program.T {body, overflow, ...} = program

      val {descend=descend, newInst=newInst, postBind=postBind,
           alloc=allocTransient, destroy=destroyAllocator} = allocator config

      val {get = addrInfo: Addr.t -> AbsValSet.t, 
           destroy = destroyAddrInfo} = 
           store (config, fn _ => AbsValSet.empty ())
      val {get = varAddrs: Sxml.Var.t -> Addr.t HashSet.t,
           destroy = destroyVarAddrs} =
         Property.destGet
         (Sxml.Var.plist,
          Property.initFun (fn _ => HashSet.new {hash=Addr.hash}))
      fun alloc (var, bind, inst) = let
         val addr = allocTransient {var=var, bind=bind, inst=inst}
      in
         HashSet.lookupOrInsert
         (varAddrs var, Addr.hash addr, 
          fn addr' => Addr.equals (addr, addr'),
          fn () => addr)
      end

      (* used for diagnostic *)
      val {get = caseInfo: Sxml.Var.t -> (Inst.t * Sxml.Con.t) list ref,
           destroy = destroyCaseInfo} =
         Property.destGet
         (Sxml.Var.plist,
          Property.initFun (fn _ => ref []))
      val caseVars: Sxml.Var.t HashSet.t = HashSet.new {hash=Sxml.Var.hash}
      fun addCaseVar var =
         HashSet.lookupOrInsert
         (caseVars, Sxml.Var.hash var,
          fn var' => Sxml.Var.equals (var, var'),
          fn () => var)

      fun newProxy () = Sxml.Var.newString "p"

      val {get = typeInfo: Sxml.Type.t -> AbsValSet.t,
           destroy = destroyTypeInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (AbsValSet.singleton o AbsVal.Base))
      val {get = lambdaInfo: Sxml.Lambda.t -> (Addr.t list * (AbsValSet.t * AbsValSet.t)) list ref,
           destroy = destroyLambdaInfo} =
         Property.destGet
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => ref []))
      (* We never use postBind with these since there's no handle block we
       * could bind them in, so we won't need to make an address *)
      val topLevelExn = AbsValSet.empty ()

      (* gets set once we first see the overflow dec *)
      val overflowVal: AbsValSet.t option ref = ref NONE

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

      fun loopExp (inst: Inst.t, env, raiseTo: AbsValSet.t, exp: Sxml.Exp.t): AbsValSet.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val resultVar = Sxml.VarExp.var result
            val (_, env') = List.fold (decs, (inst, env),
               fn (dec, (inst, env)) => loopDec (inst, env, raiseTo, dec))
         in
            envValue(env', resultVar)
         end
      and loopExp' (inst: Inst.t, env, raiseTo: AbsValSet.t, exp: Sxml.Exp.t): unit = ignore (loopExp (inst, env, raiseTo, exp))
      and loopDec (inst: Inst.t, env, raiseTo: AbsValSet.t, dec: Sxml.Dec.t): (Inst.t * env) =
         (case dec of
            Sxml.Dec.Fun {decs, ...} =>
               let
                  val env = Vector.fold(decs, env, fn ({var, lambda, ty}, env) =>
                     (var, alloc (var, Bind.LetVal (Sxml.PrimExp.Lambda lambda, ty), inst)) :: env)
                  val ninst = Vector.fold
                  (decs, inst, fn ({var, lambda, ty}, inst) =>
                  let
                     val lamExp = Sxml.PrimExp.Lambda lambda
                     val addr = envGet (env, var)
                     val freeVars = Vector.concat [freeVars lambda, freeRecVars lambda]
                     val freeVars = Vector.map(freeVars, fn v => (v, envGet(env, v)))
                     val _ = AbsValSet.<< (AbsVal.Lambda (freeVars, lambda, ty), addrInfo addr)
                   in
                      (postBind (inst, {var=var, bind=Bind.LetVal (lamExp, ty)}))
                   end)
               in
                  (ninst, env)
               end
           | Sxml.Dec.MonoVal bind => loopBind (inst, env, raiseTo, bind)
           | _ => Error.bug "allocCFA.loopDec: strange dec")
      and loopBind (inst, env, raiseTo: AbsValSet.t, bind as {var, exp, ty, ...}): (Inst.t * env) =
         let
            val addr = alloc (var, Bind.LetVal (exp, ty), inst)
            val _ = AbsValSet.<= (loopPrimExp (inst, env, raiseTo, bind), addrInfo addr)
            val env' = (var, addr) :: env
         in
            (postBind (inst, {var=var, bind=Bind.LetVal (exp, ty)}), env')
         end
      and loopPrimExp (inst, env, raiseTo, {var: Sxml.Var.t, exp: Sxml.PrimExp.t, ty: Sxml.Type.t, ...}): AbsValSet.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                           (envExpValue (env, func), fn v =>
                            case v of
                               AbsVal.Lambda (frees, lambda', lamty) =>
                                  if not (
                                    (case Sxml.Type.deArrow lamty of 
                                        (_, res) => Sxml.Type.equals (res, ty) ))
                                        then ()
                                  else
                                  let
                                     val {arg = formArg, body = body', ...} = Sxml.Lambda.dest lambda'
                                     fun rebind (v, oldAddr) =
                                        let
                                           val newAddr = alloc (v, Bind.AppFree (var, lambda', oldAddr), inst)
                                           val _ = AbsValSet.<= (addrInfo oldAddr,
                                                                 addrInfo newAddr)
                                        in
                                           (v, newAddr)
                                        end
                                     val newFree = Vector.toListMap (frees, rebind)

                                     val argAddr = envGet (env, Sxml.VarExp.var arg)
                                     val formAddr = alloc(formArg, Bind.AppArg (var, lambda', argAddr), inst)
                                     val _ = AbsValSet.<=
                                        (addrInfo argAddr,
                                         addrInfo formAddr)

                                     val newEnv = (formArg, formAddr) :: newFree

                                     (* update the instrumentation, for all the new simultaneous bindings
                                      * use the original addresses to give consistent info *)
                                     val inst = Vector.fold (frees, inst,
                                       fn ((v, addr), inst) => postBind (inst,
                                          {var=v, bind=Bind.AppFree (var, lambda', addr)}))
                                     val inst = postBind (inst, {var=formArg, bind=Bind.AppArg (var, lambda', argAddr)})


                                     val boundAddrs = List.map (newEnv, #2)

                                     (* Adjust the instrumentation to consider the body of the lambda
                                      * At this point it's seen all the (re-)bindings *)
                                     val inst = descend (inst, {var=var, exp=exp, subExp=SubExp.LambdaBody lambda'})

                                     val (raiseVal, resVal) =
                                        (case List.peek (!(lambdaInfo lambda'),
                                           fn (bound', _) => List.equals (boundAddrs, bound', Addr.equals))
                                        of
                                           SOME (_, vals) => vals
                                         | NONE =>
                                              let 
                                                 (* determinism ensures that all values that flow
                                                  * into res will flow into the other lambda
                                                  * and isolation of res ensures these are the
                                                  * only values *)
                                                 val newRaise = AbsValSet.empty ()
                                                 val _ = List.push (lambdaInfo lambda', (boundAddrs, (newRaise, res)))
                                                 val newVal = loopExp (inst, newEnv, newRaise, body')
                                                 val _ = lambdaInfo lambda' := List.map (!(lambdaInfo lambda'),
                                                    fn (bound', x) => if List.equals (boundAddrs, bound', Addr.equals)
                                                       then (bound', (newRaise, newVal))
                                                    else (bound', x))
                                              in
                                                 (newRaise, newVal)
                                              end)
                                     val _ = AbsValSet.<= (raiseVal, raiseTo)
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
                   val _ = addCaseVar (Sxml.VarExp.var test)
                   (* maintain one instance for each time we pass by a case expression
                    * we're not really going to bother with any additional flattening *)
                   val info : (Sxml.Con.t option * Addr.t option * AbsValSet.t) list ref = ref []
                   val _ =
                      case cases of
                         Sxml.Cases.Con cases => 
                         let
                            val _ = AbsValSet.addHandler
                               (envExpValue (env, test), fn v =>
                                case v of
                                   AbsVal.ConApp {con = con', arg = arg'} =>
                                      (case Vector.peek (cases, fn (Sxml.Pat.T {con, ...}, _) =>
                                          Sxml.Con.equals (con, con')) of
                                          SOME (Sxml.Pat.T {arg, ...}, caseExp) =>
                                             let
                                                val argAddrOpt = (case List.peek (!info, fn (con, _, _) =>
                                                   Option.exists (con, fn con => Sxml.Con.equals (con', con))) of
                                                   SOME (SOME _, argAddrOpt, _) => argAddrOpt
                                                 | _ =>
                                                    let
                                                       val (newAddr, env, inst) = case arg of 
                                                           NONE => (NONE, env,
                                                            descend (inst,
                                                               {var=var, exp=exp, subExp=SubExp.CaseBody (SOME (con', NONE))}))
                                                         | SOME (arg, argTy) =>
                                                             let
                                                                val addr = alloc (arg, Bind.CaseArg (con', argTy), inst)
                                                                val env' = (arg, addr) :: env
                                                                val inst = postBind (inst, {var=arg, bind=Bind.CaseArg (con', argTy)})
                                                                val inst = descend (inst,
                                                                   {var=var, exp=exp, subExp=SubExp.CaseBody (SOME (con', SOME arg)) })
                                                             in
                                                                (SOME addr, env', inst)
                                                             end
                                                       val _ = List.push (info, (SOME con', newAddr, res))
                                                       val resVal = loopExp (inst, env, raiseTo, caseExp)
                                                       val _ = AbsValSet.<= (resVal, res)
                                                       val _ = info := List.map (!info,
                                                          fn (con, a, v) => 
                                                             if Option.exists (con, fn con => Sxml.Con.equals (con', con))
                                                                then (con, a, resVal)
                                                             else (con, a, v))
                                                       val _ = List.push (caseInfo var, (inst, con'))
                                                    in
                                                       newAddr
                                                    end)
                                                val _ = 
                                                   (case (arg', argAddrOpt) of
                                                       (NONE, NONE) => true
                                                     | (SOME (_, argAddr), SOME newAddr) =>
                                                          AbsValSet.<= (addrInfo argAddr, addrInfo newAddr)
                                                     | _ => Error.bug ("allocCFA.loopPrimExp: Strange case args:" ^
                                                            Layout.toString (Layout.seq
                                                           [Option.layout (Addr.layout o #2) arg',
                                                            Layout.str " vs ",
                                                            Option.layout Addr.layout argAddrOpt,
                                                            Layout.str " on ",
                                                            Sxml.Con.layout con'])))
                                             in
                                                ()
                                             end
                                        | NONE => case default of 
                                            SOME (defExp, _) =>
                                               (case List.peek (!info, fn (con, _, _) => Option.isNone con) of
                                                 SOME _ =>
                                                    () (* already flowed in the resVal *)
                                               | NONE =>
                                                  let
                                                     val _ = List.push (info, (NONE, NONE, res))
                                                     val resVal = loopExp (inst, env, raiseTo, defExp)
                                                     val _ = info := List.map (!info,
                                                     fn (con, a, v) => if Option.isNone con
                                                        then (con, a, resVal)
                                                     else (con, a, v))
                                                     val _ = AbsValSet.<= (resVal, res)
                                                  in
                                                     ()
                                                  end)
                                          | NONE => ())
                                 (* Non- ConApp *)
                                 | _ => ())
                         in
                            ()
                         end
                       | Sxml.Cases.Word _ =>
                            Sxml.Cases.foreach (cases, fn caseExp =>
                            let
                               val inst = descend (inst,
                                  {var=var, exp=exp, subExp=SubExp.CaseBody NONE})
                               val _ =
                                  Option.foreach (default, fn (caseExp, _) =>
                                        ignore (AbsValSet.<= (loopExp (inst, env, raiseTo, caseExp), res)))
                               val _ = AbsValSet.<= (loopExp (inst, env, raiseTo, caseExp), res)
                            in
                               ()
                            end)

                in
                   res
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                let
                   val res =
                   AbsValSet.singleton (AbsVal.ConApp {con=con,
                   arg=(case arg of
                       NONE => NONE
                     | SOME arg' =>
                      let
                         val arg' = Sxml.VarExp.var arg'
                         val oldAddr = envGet (env, arg')
                         val newAddr = allocTransient (* don't really need to consider this a variable *)
                            {var=newProxy (), bind=Bind.ConArg (con, oldAddr), inst=inst}
                         val _ = AbsValSet.<= (addrInfo oldAddr, addrInfo newAddr)
                      in
                         SOME (arg', newAddr)
                      end)})
                   (* this will be happen exactly once in any sml program *)
                   val _ = if Option.exists (overflow, fn v => Sxml.Var.equals (v, var))
                           then overflowVal := (SOME res)
                           else ()
                in
                   res
                end
           | Sxml.PrimExp.Const _ =>
                typeInfo ty
           | Sxml.PrimExp.Handle {try, catch = (catchVar, catchTy), handler} =>
                let
                   val res = AbsValSet.empty ()
                   val newRaiseTo = alloc (catchVar, Bind.HandleArg catchTy, inst)
                   val tryInst = descend (inst,
                     {var=var, exp=exp, subExp = SubExp.HandleTry})
                   val _ = AbsValSet.<= (loopExp (tryInst, env, addrInfo newRaiseTo, try), res)

                   val catchInst = postBind (inst, {var=catchVar, bind=Bind.HandleArg catchTy})
                   val catchInst = descend (catchInst,
                     {var=var, exp=exp, subExp = SubExp.HandleCatch})
                   val _ = AbsValSet.<= (loopExp (catchInst, (catchVar, newRaiseTo) :: env, raiseTo, handler), res)
                in
                   res
                end
           | Sxml.PrimExp.Lambda lambda =>
                let
                   val freeVars = Vector.concat [freeVars lambda, freeRecVars lambda]
                   val freeVars = Vector.map(freeVars, fn v => (v, envGet(env, v)))
                in
                   AbsValSet.singleton (AbsVal.Lambda (freeVars, lambda, ty))
                end
           | Sxml.PrimExp.PrimApp {prim, args, ...} =>
                let
                   val res = AbsValSet.empty ()
                   fun arg i = envExpValue (env, Vector.sub (args, i))
                   datatype z = datatype Sxml.Prim.Name.t
                   val _ =
                      case Sxml.Prim.name prim of
                         Array_uninit =>
                            let
                               val p = newProxy ()
                               val pa = alloc (p, Bind.PrimAddr (prim, ty), inst)
                            in
                               ignore (AbsValSet.<< (AbsVal.Array pa, res))
                            end
                       | Array_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Array pa => ignore (AbsValSet.<= (addrInfo pa, res))
                              | _ => ())
                       | Array_update =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Array pa => ignore (AbsValSet.<= (arg 2, addrInfo pa))
                               | _ => ());
                             ignore (AbsValSet.<= (typeInfo Sxml.Type.unit, res)))
                       | Array_toVector =>
                            let
                               val p = newProxy ()
                               val pv = alloc (p, Bind.PrimAddr (prim, ty), inst)
                            in
                               AbsValSet.addHandler
                               (arg 0, fn v =>
                                case v of
                                   AbsVal.Array pa => ignore (AbsValSet.<= (addrInfo pa, addrInfo pv))
                                 | _ => ());
                               ignore (AbsValSet.<< (AbsVal.Vector pv, res))
                            end
                       | Ref_assign =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Ref pr => ignore (AbsValSet.<= (arg 1, addrInfo pr))
                               | _ => ());
                             ignore (AbsValSet.<= (typeInfo Sxml.Type.unit, res)))
                       | Ref_deref =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Ref pr => ignore (AbsValSet.<= (addrInfo pr, res))
                              | _ => ())
                       | Ref_ref =>
                            let
                               val p = newProxy ()
                               val pr = alloc (p, Bind.PrimAddr (prim, ty), inst)
                            in
                               ignore (AbsValSet.<= (arg 0, addrInfo pr));
                               ignore (AbsValSet.<< (AbsVal.Ref pr, res))
                            end
                       | Weak_new =>
                            let
                               val p = newProxy ()
                               val pw = alloc (p, Bind.PrimAddr (prim, ty), inst)
                            in
                               ignore (AbsValSet.<= (arg 0, addrInfo pw));
                               ignore (AbsValSet.<< (AbsVal.Weak pw, res))
                            end
                       | Weak_get =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Weak pw => ignore (AbsValSet.<= (addrInfo pw, res))
                              | _ => ())
                       | Vector_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Vector pv => ignore (AbsValSet.<= (addrInfo pv, res))
                              | _ => ())
                       | Vector_vector =>
                            let
                               val p = newProxy ()
                               val pv = alloc (p, Bind.PrimAddr (prim, ty), inst)
                            in
                               ignore (AbsValSet.<< (AbsVal.Vector pv, res))
                            end
                       | _ =>
                            let
                               val _ = AbsValSet.<= (if Sxml.Type.equals(ty, Sxml.Type.bool)
                                  then AbsValSet.fromList [AbsVal.ConApp {con= Sxml.Con.truee, arg= NONE},
                                                           AbsVal.ConApp {con= Sxml.Con.falsee, arg= NONE}]
                                  else (typeInfo ty), res)
                               val _ = if Sxml.Prim.mayOverflow prim
                                       then (case !overflowVal of
                                           SOME v => ignore (AbsValSet.<= (v, raiseTo))
                                         | NONE => ())
                                       else ()
                            in
                               ()
                            end
                in
                   res
                end
           | Sxml.PrimExp.Profile _ =>
                typeInfo ty
           | Sxml.PrimExp.Raise {exn, ...} =>
                let
                   val _ = AbsValSet.<= (envExpValue (env, exn), raiseTo)
                in
                   AbsValSet.empty ()
                end
           | Sxml.PrimExp.Select {tuple, offset} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                          (envExpValue (env, tuple), fn v =>
                           case v of
                              AbsVal.Tuple xs' =>
                                 ignore (AbsValSet.<= (addrInfo (#2 (Vector.sub (xs', offset))), res))
                            | _ => ())
                in
                   res
                end
           | Sxml.PrimExp.Tuple xs =>
                AbsValSet.singleton (AbsVal.Tuple (Vector.map (xs,
                     fn v => (Sxml.VarExp.var v, envGet(env, Sxml.VarExp.var v)))))
           | Sxml.PrimExp.Var x =>
                envExpValue (env, x)
                )


      val _ = loopExp' (newInst (), [], topLevelExn, body)

      val _ =
         Control.diagnostics
         (fn display =>
          ((HashSet.foreach (caseVars,
          fn var => (display o Layout.seq)
             [Layout.str "val ",
              Sxml.Var.layout var,
              Layout.str " = case of ",
              List.layout (fn (inst, con) =>
                 Layout.seq
                    [Layout.str "(",
                     Inst.layout inst,
                     Layout.str " ",
                     Sxml.Con.layout con,
                     Layout.str ")"]) (!(caseInfo var))]));
          (Sxml.Exp.foreachBoundVar
           (body, fn (x, _, _) =>
            List.foreach (HashSet.toList (varAddrs x), fn addr =>
            (display o Layout.seq)
            [Sxml.Var.layout x, Layout.str " @ ",
             Addr.layout addr, Layout.str " : ", 
             AbsValSet.layout (addrInfo addr)])))))

      fun allValues var = List.removeDuplicates
         (List.concatMap (HashSet.toList (varAddrs var),
            fn s => AbsValSet.getElements (addrInfo s)),
          AbsVal.equals)
      fun canRaise lam = List.exists 
         (!(lambdaInfo lam),
          fn (_, (raiseVal, _)) => List.exists
             (AbsValSet.getElements raiseVal,
              fn v => case v of
                  AbsVal.ConApp _ => true
                | _ => false))


      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, argTy, resTy, ...} => List.removeDuplicates (
            List.keepAllMap (allValues func, fn absVal =>
               case absVal of
                  AbsVal.Lambda (_, lam, ty) => if compatibleLambda(ty, argTy, resTy)
                  then SOME lam
                  else NONE
                | _ => NONE),
                  Sxml.Lambda.equals)
      fun caseUsed {res: Sxml.Var.t,
                    con: Sxml.Con.t} =
         List.exists (!(caseInfo res),
            fn (_, con') => Sxml.Con.equals (con, con'))
      val knownCon: {res: Sxml.Var.t} ->
             {arg: Sxml.VarExp.t option,
              con: Sxml.Con.t} option =
         fn {res} =>
            let
               val absVals = List.keepAllMap(allValues res, fn absVal =>
                  case absVal of
                     AbsVal.ConApp {con, arg} => SOME {con=con,
                        arg=Option.map(arg, Sxml.VarExp.mono o #1)}
                   | _ => NONE)
            in
               case absVals of
                   [{con, arg=NONE}] => SOME {con=con, arg=NONE}
                 | _ => NONE
            end

      fun varUsed {var: Sxml.Var.t} =
         case allValues var of
             [] => false
           | _ => true

      val destroy = fn () =>
         (destroyCaseInfo ();
          destroyLambdaFree ();
          destroyLambdaInfo ();
          destroyAddrInfo ();
          destroyVarAddrs ();
          destroyTypeInfo ();
          destroyAllocator ())
   in
      {canRaise=canRaise, caseUsed=caseUsed, cfa=cfa, destroy=destroy, knownCon=knownCon, varUsed=varUsed}
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
