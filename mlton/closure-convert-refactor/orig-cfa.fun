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

structure Config = struct type t = unit end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

structure Value = AbstractValue (structure Sxml = Sxml)

fun cfa (_: {config: Config.t}): t =
   fn {program: Sxml.Program.t} =>
   let
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

      fun newVar (x, v) = setVarInfo (x, {value = v})
      fun varExpValues xs = Vector.map (xs, varExpValue)
      fun loopExp (e: Sxml.Exp.t): Value.t =
         let
            val {decs, result} = Sxml.Exp.dest e
            val () = List.foreach (decs, loopDec)
         in
            varExpValue result
         end
      and loopDec (d: Sxml.Dec.t): unit =
         (case d of
             Sxml.Dec.Fun {decs, ...} =>
                (Vector.foreach
                 (decs, fn {var, ty, ...} =>
                  newVar (var, Value.fromType ty));
                 Vector.foreach
                 (decs, fn {var, ty, lambda, ...} =>
                  Value.unify (varValue var, loopLambda (lambda, ty))))
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
                            Value.coerce {from = arg,
                                          to = varValue formal};
                            Value.coerce {from = expValue body,
                                          to = result}
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
             | Sxml.PrimExp.Lambda lambda => set (loopLambda (lambda, ty))
             | Sxml.PrimExp.PrimApp {prim, args, ...} =>
                  set (Value.primApply {prim = prim,
                                        args = varExpValues args,
                                        resultTy = ty})
             | Sxml.PrimExp.Profile _ => new' ()
             | Sxml.PrimExp.Raise _ => new' ()
             | Sxml.PrimExp.Select {tuple, offset} =>
                  set (Value.select (varExpValue tuple, offset))
             | Sxml.PrimExp.Tuple xs =>
                  if Value.typeIsFirstOrder ty
                     then new' ()
                     else set (Value.tuple (Vector.map (xs, varExpValue)))
             | Sxml.PrimExp.Var x => set (varExpValue x)
         end
      and loopLambda (lambda: Sxml.Lambda.t, ty: Sxml.Type.t): Value.t =
         let
            val {arg, argType, body, ...} = Sxml.Lambda.dest lambda
            val _ = newVar (arg, Value.fromType argType)
            val _ = loopExp body
         in
            Value.lambda (lambda, ty)
         end
      val _ = loopExp body

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
          Sxml.Exp.foreachBoundVar
          (body, fn (var, _, _) =>
           remVarInfo var))
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "OrigCFA")
   (cfa config)

fun scan _ charRdr strm0 =
   case Scan.string "ocfa" charRdr strm0 of
      SOME ((), strm1) => SOME (cfa {config = ()}, strm1)
    | _ => NONE

end
