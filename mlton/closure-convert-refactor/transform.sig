(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature TRANSFORM_STRUCTS =
   sig
      structure Ssa: SSA
      structure Sxml: SXML
      sharing Sxml.Atoms = Ssa.Atoms
   end

signature TRANSFORM =
   sig
      include TRANSFORM_STRUCTS

      structure Config:
         sig
            type t
            val init: t
         end

      type t = {program: Sxml.Program.t,
                cfa: {arg: Sxml.Var.t,
                      argTy: Sxml.Type.t,
                      func: Sxml.Var.t,
                      res: Sxml.Var.t,
                      resTy: Sxml.Type.t} ->
                     Sxml.Lambda.t list} ->
               {program: Ssa.Program.t,
                destroy: unit -> unit}

      val transform: {config: Config.t} -> t

      val scan: ((char, 'a) StringCvt.reader -> (t, 'a) StringCvt.reader) ->
                (char, 'a) StringCvt.reader ->
                (t, 'a) StringCvt.reader
   end
