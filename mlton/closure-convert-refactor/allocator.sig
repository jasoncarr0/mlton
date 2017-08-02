(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ALLOCATOR_STRUCTS = 
   sig
      structure Sxml: SXML
   end

signature ALLOCATOR =
   sig
      include ALLOCATOR_STRUCTS

      structure Config:
         sig
            type t
            val scan: t Parse.t
         end
      structure Inst:
         sig
            type t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
            val new: Config.t -> t
            val preEval: t * {var: Sxml.Var.t,
                              exp: Sxml.PrimExp.t} -> t
            val postBind: t * {var: Sxml.Var.t,
                               exp: Sxml.PrimExp.t}-> t
         end
      structure Addr:
         sig
            type t
            val alloc: Sxml.Var.t * Inst.t -> t
            val realloc: {addr: t,
                          inst: Inst.t,
                          var: Sxml.Var.t} -> t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
            val store: {empty: t -> 'a} -> 
                        {get: t -> 'a,
                         destroy: unit -> unit}
         end
end
