(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature GLOBALIZE_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature GLOBALIZE =
   sig
      include GLOBALIZE_STRUCTS

      val globalize: {program: Sxml.Program.t,
                      freeVars: Sxml.Lambda.t -> Sxml.Var.t vector} ->
                     {isGlobal: Sxml.Var.t -> bool,
                      destroy: unit -> unit}
   end
