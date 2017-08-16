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
         {caseUsed: {test: Sxml.Var.t,
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

structure Config = struct type t = {baseCFA: t} end

fun cfa {config = {baseCFA}: Config.t}: t =
   fn {program: Sxml.Program.t} =>
   let
      val {caseUsed=caseUsed, cfa=baseCFA, destroy=destroyBaseCFA,
           knownCon=knownCon, varUsed=varUsed} =
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
      {caseUsed=caseUsed, cfa=cfa, destroy=destroy,
       knownCon=knownCon, varUsed=varUsed}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "SynKnownCFA")
   (cfa config)

local
   open Parse
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$
   fun mkCfg t = {config = {baseCFA = t}}
in
   fun scan scanRec =
      str "synkwn(" *>
      cfa <$> mkCfg <$> scanRec
      <* str ")"
end
end
