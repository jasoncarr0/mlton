(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* The simple monomorphic-type-based control-flow analysis:
 * approximate the set of lambdas that might be called at an
 * application by all lambdas in the program of the appropriate type.
 *)
functor TyCFA (S: CFA_STRUCTS): CFA =
struct

open S

structure Config = struct type t = unit end

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

fun cfa (_: {config: Config.t}): t =
   fn {program: Sxml.Program.t} =>
   let
      val Sxml.Program.T {body, ...} = program
      val {get = arrowInfo: Sxml.Type.t -> Sxml.Lambda.t list ref,
           destroy = destroyArrowInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (fn ty =>
                            if Option.isSome (Sxml.Type.deArrowOpt ty)
                               then ref []
                               else Error.bug "TyCFA.arrowInfo: non-arrow"))

      val () =
         Sxml.Exp.foreachPrimExp
         (body, fn (_, ty, exp) =>
          case exp of
             Sxml.PrimExp.Lambda lam =>
                List.push (arrowInfo ty, lam)
           | _ => ())

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {argTy, resTy, ...} =>
         ! (arrowInfo (Sxml.Type.arrow (argTy, resTy)))

      fun canRaise _ = true
      fun caseUsed _ = true
      fun knownCon _ = NONE
      fun varUsed _ = true

      val destroy = fn () =>
         destroyArrowInfo ()
   in
      {canRaise=canRaise, caseUsed=caseUsed, cfa=cfa, destroy=destroy,
       knownCon=knownCon, varUsed=varUsed}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "TyCFA")
   (cfa config)

local 
   open Parse
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$
in
   fun scan _ = cfa <$> ({config=()} <$ Parse.str "tycfa")
end
end
