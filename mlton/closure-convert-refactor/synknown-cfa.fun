(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* The simple known-function refinement of a base control-flow
 * analysis using syntactic heuristics.
 *)
functor SynKnownCFA (S: CFA_STRUCTS): CFA =
struct

open S

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

structure Config = struct type t = {baseCFA: t} end

fun cfa {config = {baseCFA}: Config.t}: t =
   fn {program: Sxml.Program.t} =>
   let
      val {cfa = baseCFA, destroy = destroyBaseCFA} =
         baseCFA {program = program}

      val Sxml.Program.T {body, ...} = program
      val {get = varInfo: Sxml.Var.t -> Sxml.Lambda.t option,
           set = setVarInfo, destroy = destroyVarInfo} =
         Property.destGetSetOnce
         (Sxml.Var.plist, Property.initConst NONE)

      val () =
         Sxml.Exp.foreachPrimExp
         (body, fn (var, _, exp) =>
          case exp of
             Sxml.PrimExp.Lambda lam =>
                setVarInfo (var, SOME lam)
           | _ => ())

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn call as {func, ...} =>
         let
            val lambdas = baseCFA call
         in
            case varInfo func of
               NONE => lambdas
             | SOME knownLambda =>
                  List.keepAll
                  (lambdas, fn lambda =>
                   Sxml.Lambda.equals (lambda, knownLambda))
         end

      val destroy = fn () =>
         (destroyBaseCFA ();
          destroyVarInfo ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "SynKnownCFA")
   (cfa config)

fun scan scanCFARec charRdr strm0 =
   case Scan.string "synkwn" charRdr strm0 of
      SOME ((), strm1) =>
         (case charRdr strm1 of
             SOME (#"(", strm2) =>
                (case scanCFARec charRdr strm2 of
                    SOME (baseCFA, strm3) =>
                       (case charRdr strm3 of
                           SOME (#")", strm4) =>
                              SOME (cfa {config = {baseCFA = baseCFA}}, strm4)
                         | _ => NONE)
                  | _ => NONE)
           | _ => NONE)
    | _ => NONE

end
