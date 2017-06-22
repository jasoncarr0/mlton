(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature CFA_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature CFA =
   sig
      include CFA_STRUCTS

      structure Config:
         sig
            type t
         end

      type t = {program: Sxml.Program.t} ->
               {cfa: {arg: Sxml.Var.t,
                      argTy: Sxml.Type.t,
                      func: Sxml.Var.t,
                      res: Sxml.Var.t,
                      resTy: Sxml.Type.t} ->
                     Sxml.Lambda.t list,
                destroy: unit -> unit}

      val cfa: {config: Config.t} -> t

      val scan: ((char, 'a) StringCvt.reader -> (t, 'a) StringCvt.reader) ->
                (char, 'a) StringCvt.reader ->
                (t, 'a) StringCvt.reader
   end
