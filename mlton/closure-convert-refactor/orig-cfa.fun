(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor OrigCFA (S: CFA_STRUCTS): CFA =
struct

open S

structure Config =
   struct
      datatype t = T of {reachabilityExt: bool}
      val init = T {reachabilityExt = false}
      fun updateReachabilityExt (T {...}: t, reachabilityExt) =
         T {reachabilityExt = reachabilityExt}
   end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

structure Value = AbstractValue (structure Sxml = Sxml)

fun cfa {config: Config.t}: t =
   fn {program: Sxml.Program.t} =>
   let
      val Config.T {reachabilityExt} = config
      val Sxml.Program.T {datatypes, body, ...} = program

      val {get = conInfo: Sxml.Con.t -> {argValue: Value.t option},
           set = setConInfo, rem = remConInfo} =
         Property.getSetOnce
         (Sxml.Con.plist,
          Property.initRaise ("OrigCFA.conInfo", Sxml.Con.layout))
      val conArgValue = #argValue o conInfo
      val {get = varInfo: Sxml.Var.t -> {value: Value.t},
           set = setVarInfo, rem = remVarInfo} =
         Property.getSetOnce
         (Sxml.Var.plist,
          Property.initRaise ("OrigCFA.varInfo", Sxml.Var.layout))
      val varValue = #value o varInfo
      val varExpValue = varValue o Sxml.VarExp.var
      val expValue = varExpValue o Sxml.Exp.result
      val {get = lambdaInfo: Sxml.Lambda.t -> {visited: bool ref},
           rem = remLambdaInfo} =
         Property.get
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => {visited = ref false}))
      val lambdaVisited = ! o #visited o lambdaInfo
      val setLambdaVisited = fn lambda => #visited (lambdaInfo lambda) := true

      (* Do the flow analysis.
       *)
      val _ =
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach
          (cons, fn {con, arg} =>
           setConInfo (con, {argValue =
                             case arg of
                                NONE => NONE
                              | SOME t => SOME (Value.fromType t)})))

      val newVar =
         if reachabilityExt
            then let
                    val _ =
                       Sxml.Exp.foreachBoundVar
                       (body, fn (x, _, ty) =>
                        setVarInfo (x, {value = Value.fromType ty}))
                 in
                    fn (x, v) => Value.unify (varValue x, v)
                 end
            else fn (x, v) => setVarInfo (x, {value = v})
      fun loopExp (e: Sxml.Exp.t): Value.t =
         let
            val {decs, result} = Sxml.Exp.dest e
            val () = List.foreach (decs, loopDec)
         in
            varExpValue result
         end
      and loopExp' (e: Sxml.Exp.t): unit = ignore (loopExp e)
      and loopDec (d: Sxml.Dec.t): unit =
         (case d of
             Sxml.Dec.Fun {decs, ...} =>
                (Vector.foreach
                 (decs, fn {var, ty, ...} =>
                  newVar (var, Value.fromType ty));
                 Vector.foreach
                 (decs, fn {var, lambda, ...} =>
                  Value.unify (varValue var, loopLambda lambda)))
           | Sxml.Dec.MonoVal b => loopBind b
           | _ => Error.bug "OrigCFA.loopDec: strange dec")
      and loopBind {var, ty, exp} =
         let
            fun set v = newVar (var, v)
            fun new () =
               let val v = Value.fromType ty
               in set v; v
               end
            val new' = ignore o new
         in
            case exp of
               Sxml.PrimExp.App {func, arg} =>
                  let
                     val arg = varExpValue arg
                     val result = new ()
                     val _ =
                        Value.addHandler
                        (varExpValue func, fn lambda =>
                         let
                            val {arg = formal, body, ...} =
                               Sxml.Lambda.dest lambda
                         in
                            Value.coerce {from = arg, to = varValue formal};
                            if reachabilityExt andalso not (lambdaVisited lambda)
                               then (setLambdaVisited lambda; loopExp' body)
                               else ();
                            Value.coerce {from = expValue body, to = result}
                         end)
                  in ()
                  end
             | Sxml.PrimExp.Case {cases, default, ...} =>
                  let
                     val result = new ()
                     fun branch e =
                        Value.coerce {from = loopExp e, to = result}
                     fun handlePat (Sxml.Pat.T {con, arg, ...}) =
                        case (arg, conArgValue con) of
                           (NONE, NONE) => ()
                         | (SOME (x, _), SOME v) => newVar (x, v)
                         | _ => Error.bug "OrigCFA.loopBind: Case"
                     val _ = Sxml.Cases.foreach' (cases, branch, handlePat)
                     val _ = Option.app (default, branch o #1)
                  in ()
                  end
             | Sxml.PrimExp.ConApp {con, arg, ...} =>
                  let
                     val _ =
                        case (arg, conArgValue con) of
                           (NONE, NONE) => ()
                         | (SOME x, SOME v) =>
                              Value.coerce {from = varExpValue x, to = v}
                         | _ => Error.bug "OrigCFA.loopBind: ConApp"
                  in
                     new' ()
                  end
             | Sxml.PrimExp.Const _ => new' ()
             | Sxml.PrimExp.Handle {try, catch = (x, t), handler} =>
                  let
                     val result = new ()
                  in
                     Value.coerce {from = loopExp try, to = result};
                     newVar (x, Value.fromType t);
                     Value.coerce {from = loopExp handler, to = result}
                  end
             | Sxml.PrimExp.Lambda lambda => set (loopLambda lambda)
             | Sxml.PrimExp.PrimApp {prim, targs, args, ...} =>
                  if Vector.forall (targs, Value.typeIsFirstOrder)
                     then new' ()
                  else
                  let
                     fun arg i = varExpValue (Vector.sub (args, i))
                     fun bug (k, v) =
                        (Error.bug o String.concat)
                        ["OrigCFA.loopPrimExp: non-", k,
                         " (got ", Layout.toString (Value.layout v),
                         " for ", Sxml.Prim.Name.toString (Sxml.Prim.name prim), ")"]
                     datatype z = datatype Sxml.Prim.Name.t
                  in
                     case Sxml.Prim.name prim of
                        Array_sub =>
                           (case Value.dest (arg 0) of
                               Value.Array x => set x
                             | _ => bug ("Array", arg 0))
                      | Array_update =>
                           (case Value.dest (arg 0) of
                               Value.Array x => Value.coerce {from = arg 2, to = x}
                             | _ => bug ("Array", arg 0);
                            new' ())
                      | Array_toVector =>
                           let val result = new ()
                           in
                              case (Value.dest (arg 0), Value.dest result) of
                                 (Value.Array x, Value.Vector y) =>
                                    (* Can't do a coercion here because that would imply
                                     * walking over each element of the array and coercing it.
                                     *)
                                    Value.unify (x, y)
                               | (Value.Array _, _) => bug ("Vector", result)
                               | _ => bug ("Array", arg 0)
                           end
                      | Ref_assign =>
                           (case Value.dest (arg 0) of
                               Value.Ref x => Value.coerce {from = arg 1, to = x}
                             | _ => bug ("Ref", arg 0);
                            new' ())
                      | Ref_deref =>
                           (case Value.dest (arg 0) of
                               Value.Ref x => set x
                             | _ => bug ("Ref", arg 0))
                      | Ref_ref =>
                           let val result = new ()
                           in
                              case Value.dest result of
                                 Value.Ref x => Value.coerce {from = arg 0, to = x}
                               | _ => bug ("Ref", result)
                           end
                      | Weak_new =>
                           let val result = new ()
                           in
                              case Value.dest result of
                                 Value.Weak x => Value.coerce {from = arg 0, to = x}
                               | _ => bug ("Weak", result)
                           end
                      | Weak_get =>
                           (case Value.dest (arg 0) of
                               Value.Weak x => set x
                             | _ => bug ("Weak", arg 0))
                      | Vector_length => new' ()
                      | Vector_sub =>
                           (case Value.dest (arg 0) of
                               Value.Vector x => set x
                             | _ => bug ("Vector", arg 0))
                      | _ => new' ()
                  end
             | Sxml.PrimExp.Profile _ => new' ()
             | Sxml.PrimExp.Raise _ => new' ()
             | Sxml.PrimExp.Select {tuple, offset} =>
                  if Value.typeIsFirstOrder ty
                     then new' ()
                     else (case Value.dest (varExpValue tuple) of
                              Value.Tuple vs => set (Vector.sub (vs, offset))
                            | _ => Error.bug "OrigCFA.loopPrimExp: non-tuple")
             | Sxml.PrimExp.Tuple xs =>
                  if Value.typeIsFirstOrder ty
                     then new' ()
                     else set (Value.tuple (Vector.map (xs, varExpValue)))
             | Sxml.PrimExp.Var x => set (varExpValue x)
         end
      and loopLambda (lambda: Sxml.Lambda.t): Value.t =
         let
            val {arg, argType, body, ...} = Sxml.Lambda.dest lambda
            val _ = newVar (arg, Value.fromType argType)
            val _ =
               if reachabilityExt
                  then ()
                  else loopExp' body
         in
            Value.lambda lambda
         end
      val _ = loopExp' body

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, ...} =>
         case Value.dest (varValue func) of
            Value.Lambdas lambdas => lambdas
          | _ => Error.bug "OrigCFA.cfa: non-lambda"

      val destroy = fn () =>
         (Value.destroy ();
          Vector.foreach
          (datatypes, fn {cons, ...} =>
           Vector.foreach
           (cons, fn {con, ...} =>
            remConInfo con));
          Sxml.Exp.foreach
          {exp = body,
           handleExp = ignore,
           handlePrimExp = (fn (_, _, e) =>
                            case e of
                               Sxml.PrimExp.Lambda lambda => remLambdaInfo lambda
                             | _ => ()),
           handleBoundVar = (fn (var, _, _) => remVarInfo var),
           handleVarExp = ignore})
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "OrigCFA")
   (cfa config)

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
      case Scan.string "ocfa" charRdr strm0 of
         SOME ((), strm1) =>
            (case charRdr strm1 of
                SOME (#"(", strm2) => scanNameArgs (nameArgScans, Config.init) strm2
              | _ => NONE)
       | _ => NONE
   end

end
