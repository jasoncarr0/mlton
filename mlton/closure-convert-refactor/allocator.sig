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

      structure Addr:
         sig
            type t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
         end
      structure Inst:
         sig
            type t
            val layout: t -> Layout.t
            val equals: t * t -> bool
         end
      structure Config:
         sig
            type t
         end
      val new: Config.t -> Inst.t
      val postBind: Inst.t * Sxml.Var.t -> Inst.t
      val preEval: Inst.t * Sxml.PrimExp.t -> Inst.t

      val alloc: Sxml.Var.t * Inst.t -> Addr.t

      val store: {empty: Addr.t -> 'a} -> 
                        {get: Addr.t -> 'a,
                         coalesce: Sxml.Var.t -> (Addr.t * 'a) list,
                         destroy: Sxml.Var.t -> unit}
      val scan: Config.t Parse.t
   end
