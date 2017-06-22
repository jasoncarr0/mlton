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
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

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

      val destroy = fn () =>
         destroyArrowInfo ()
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "TyCFA")
   (cfa config)

fun scan _ charRdr strm0 =
   case Scan.string "tycfa" charRdr strm0 of
      SOME ((), strm1) => SOME (cfa {config = ()}, strm1)
    | _ => NONE

end
