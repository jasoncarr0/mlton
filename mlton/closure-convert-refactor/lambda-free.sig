(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature LAMBDA_FREE_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature LAMBDA_FREE =
   sig
      include LAMBDA_FREE_STRUCTS

      (*
       * For lambdas bound in a Fun dec, freeVars gives the union of the
       * frees of the entire group of mutually recursive functions.  Hence,
       * freeVars for every lambda in a single Fun dec is the same.
       * Furthermore, for a lambda bound in a Fun dec, freeRecVars gives
       * the list of other funs bound in the same dec that the lambda refers
       * to.  For example:
       *
       * val rec f = fn x => ... y ... g ... f ...
       * and g = fn z => ... f ... w ...
       *
       * freeVars(fn x =>) = [y, w]
       * freeVars(fn z =>) = [y, w]
       * freeRecVars(fn x =>) = [g, f]
       * freeRecVars(fn z =>) = [f]
       *)
      val lambdaFree: {program: Sxml.Program.t} ->
                      {freeVars: Sxml.Lambda.t -> Sxml.Var.t vector,
                       freeRecVars: Sxml.Lambda.t -> Sxml.Var.t vector,
                       destroy: unit -> unit}
   end
