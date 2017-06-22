(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor LambdaFree (S: LAMBDA_FREE_STRUCTS): LAMBDA_FREE =
struct

open S
open Sxml

structure Status =
   struct
      datatype t = Unseen | Free | Bound
   end
datatype status = datatype Status.t

fun lambdaFree {program: Program.t} =
   let
      val Program.T {body, overflow, ...} = program
      val overflow = valOf overflow

      val {get = lambdaInfo: Lambda.t -> {freeVars: Var.t vector,
                                          freeRecVars: Var.t vector},
           set = setLambdaInfo, destroy = destroyLambdaInfo} =
         Property.destGetSetOnce
         (Lambda.plist,
          Property.initRaise ("LambdaFree.lambdaInfo", Lambda.layout))

      val bogusFrees = ref []
      val {get = varInfo: Var.t -> {frees: Var.t list ref ref,
                                    status: Status.t ref},
           rem = remVarInfo} =
         Property.get
         (Var.plist,
          Property.initFun (fn _ => {frees = ref bogusFrees, status = ref Unseen}))

      type scope = {frees: Var.t list ref,
                    get: Var.t -> Status.t,
                    set: Var.t * Status.t -> unit}
      fun withScope ({get, set, frees}: scope) =
         let
            fun bindVar (x: Var.t) = set (x, Bound)
            fun visitVar (x: Var.t) =
               case get x of
                  Unseen => (set (x, Free); List.push (frees, x))
                | _ => ()
            val visitVarExp = visitVar o VarExp.var
         in
            {bindVar = bindVar,
             visitVar = visitVar,
             visitVars = fn xs => Vector.foreach (xs, visitVar),
             visitVarExp = visitVarExp,
             visitVarExps = fn xs => Vector.foreach (xs, visitVarExp)}
         end

      (*
        newScopeRes/newScope is invoked whenever there is a need to
        consider a new scope while looking for free variables. Its
        only parameter is a function taking a record that represents a
        scope supporting "setting" and "getting" variable statuses.
        The intent is that `th` will continue traversing the program
        in the current scope while aggregating variable statuses.

        Initially, newScopeRes creates a reference to a list of
        variables (`frees`). Its purpose is twofold:
          - It is a unique identifier for every encountered scope.
          - It is utilized by `th` to aggregate all variabes

        Since each variable has an associated status, updating every
        single status in the program would be unreasonably slow. Thus,
        we delay updating the status by associating each variable with
        the last scope for which that variable was seen. If the
        variable has been unmentioned until this point in the current
        scope, then we save its last scope and status, and
        "initialize" it to be Unseen.  This is achieved by having
        `get` and `set` use the `statusRef` function.

        After setting up these operations, we perform `th`, and then
        recover every variable's previous status and scope so that we
        may continue traversing the program.
       *)
      fun newScopeRes (th: {frees: Var.t list ref,
                            get:   Var.t -> Status.t,
                            set:   Var.t * Status.t -> unit} -> 'a) : 'a * Var.t vector =
         let
            val frees = ref []
            val undo = ref []
            fun statusRef x =
               let
                  val {frees = freesRef, status = statusRef, ...} = varInfo x
                  val curFrees = !freesRef
                  val curStatus = !statusRef
               in
                  if frees = curFrees
                     then ()
                     else (List.push (undo, fn () => freesRef := curFrees);
                           freesRef := frees;
                           List.push (undo, fn () => statusRef := curStatus);
                           statusRef := Unseen)
                  ; statusRef
               end
            fun get x = !(statusRef x)
            fun set (x, s) = statusRef x := s
            val res = th {frees = frees, get = get, set = set}
            val _ = List.foreach (!undo, fn th => th ())
         in
            (res, Vector.fromList (!frees))
         end
      fun newScope th = let val ((), frees) = newScopeRes th
                        in frees
                        end

      fun visitExp (exp, s) =
         let
            val {visitVarExp, ...} = withScope s
            val {decs, result} = Exp.dest exp
         in
            List.foreach (decs, fn dec => visitDec (dec, s));
            visitVarExp result
         end
      and visitDec (dec, s) =
         let
            val {bindVar, visitVars, ...} = withScope s
         in
            case dec of
               Dec.MonoVal {var, exp, ...} => (visitPrimExp (exp, s); bindVar var)
             | Dec.Fun {decs, ...} =>
                  let
                     val {get = recVar : Var.t -> bool,
                          set = setRecVar, destroy = destroyRecVar} =
                        Property.destGetSetOnce (Var.plist, Property.initConst false)
                     val _ = Vector.foreach (decs, fn {var, ...} => setRecVar (var, true))
                     val (decs, freeVars) =
                        newScopeRes
                        (fn s =>
                         let
                            val {visitVar, ...} = withScope s
                         in
                            Vector.map
                            (decs, fn {var, lambda, ...} =>
                             {var = var,
                              lambda = lambda,
                              freeRecVars = Vector.keepAll
                                            (visitLambda lambda, fn x =>
                                             if recVar x
                                                then true
                                                else (visitVar x; false))})
                         end)
                     val _ = destroyRecVar ()
                     val _ =
                        Vector.foreach
                        (decs, fn {var, lambda, freeRecVars} =>
                         (setLambdaInfo (lambda, {freeVars = freeVars, freeRecVars = freeRecVars});
                          bindVar var))
                  in
                     visitVars freeVars
                  end
             | _ => Error.bug "LambdaFree.visitDec: strange dec"
         end
      and visitPrimExp (exp, s) =
         let
            val {bindVar, visitVar, visitVars, visitVarExp, visitVarExps, ...} = withScope s
            val visitExp = fn exp => visitExp (exp, s)
         in
            case exp of
               PrimExp.App {func, arg} => (visitVarExp func; visitVarExp arg)
             | PrimExp.Case {test, cases, default} =>
                  (visitVarExp test
                   ; Cases.foreach' (cases, visitExp,
                                     fn Pat.T {arg, ...} =>
                                     Option.app (arg, fn (arg, _) => bindVar arg))
                   ; Option.app (default, visitExp o #1))
             | PrimExp.ConApp {arg, ...} => Option.app (arg, visitVarExp)
             | PrimExp.Const _ => ()
             | PrimExp.Handle {try, catch = (var, _), handler} =>
                  (visitExp try; bindVar var; visitExp handler)
             | PrimExp.Lambda lambda =>
                  let
                     val xs = visitLambda lambda
                  in
                     setLambdaInfo (lambda, {freeVars = xs, freeRecVars = Vector.new0 ()});
                     visitVars xs
                  end
             | PrimExp.PrimApp {prim, args, ...} =>
                  (if Prim.mayOverflow prim
                      then visitVar overflow
                      else ();
                   visitVarExps args)
             | PrimExp.Profile _ => ()
             | PrimExp.Raise {exn, ...} => visitVarExp exn
             | PrimExp.Select {tuple, ...} => visitVarExp tuple
             | PrimExp.Tuple xs => visitVarExps xs
             | PrimExp.Var x => visitVarExp x
         end
      and visitLambda (l: Lambda.t) : Var.t vector =
         let
            val {arg, body, ...} = Lambda.dest l
         in
            newScope (fn s =>
                      let val {bindVar, ...} = withScope s
                      in bindVar arg; visitExp (body, s)
                      end)
         end
      val frees = newScope (fn s => visitExp (body, s))
      val _ =
         if Vector.isEmpty frees
            then ()
            else Error.bug ("LambdaFree.lambdaFree: program has free variables: " ^
                            Layout.toString (Vector.layout Var.layout frees))
      val () = Exp.foreachBoundVar (body, remVarInfo o #1)
   in
      {freeVars = #freeVars o lambdaInfo,
       freeRecVars = #freeRecVars o lambdaInfo,
       destroy = destroyLambdaInfo}
   end

val lambdaFree =
   Control.trace (Control.Pass, "lambdaFree")
   lambdaFree

end
