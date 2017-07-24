(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* Intersect a (non-empty) list of CFAs. *)
functor IntersectCFA (S: CFA_STRUCTS): CFA =
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

structure Config = struct type t = {baseCFAs: t list} end

val {intersect, ...} =
   List.set {equals = Sxml.Lambda.equals, layout = Sxml.Lambda.layout}

fun cfa {config = {baseCFAs}: Config.t}: t =
   fn {program: Sxml.Program.t} =>
   let
      val (baseCFAs, destroyBaseCFAs) =
         (List.unzip o List.map)
         (baseCFAs, fn cfa =>
          let
             val {cfa, destroy} = cfa {program = program}
          in
             (cfa, destroy)
          end)

      val (baseCFA0, baseCFAs) =
         case baseCFAs of
            baseCFA0::baseCFAs => (baseCFA0, baseCFAs)
          | _ => Error.bug "IntersectCFA.cfa:: empty baseCFAs"

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn call =>
         List.fold
         (baseCFAs, baseCFA0 call, fn (baseCFA, lambdas) =>
          intersect (lambdas, baseCFA call))

      val destroy = fn () =>
         List.foreach
         (destroyBaseCFAs, fn destroyBaseCFA =>
          destroyBaseCFA ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "IntersectCFA")
   (cfa config)

local
   open Parse
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$
   fun mkCfg t = {config = {baseCFAs = Vector.toList t}} 
in
   fun scan scanRec =
      str "isect" *>
      cfa <$> mkCfg <$> tuple scanRec
end
end
