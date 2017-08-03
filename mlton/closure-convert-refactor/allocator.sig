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
      structure Bind:
         sig
            type addr
            datatype t = LetVal of Sxml.PrimExp.t
                   | AppArg of (Sxml.Lambda.t * addr)
                   | AppFree of (Sxml.Lambda.t * addr)
                   | ConArg of (Sxml.Con.t * addr)
                   | CaseArg of Sxml.Con.t
                   | HandleArg
         end
      structure SubExp:
         sig
            datatype t = LambdaBody of Sxml.Lambda.t
                       | CaseBody of (Sxml.Con.t * Sxml.Var.t option) option
                       | HandleTry
                       | HandleCatch
         end
      structure Inst:
         sig
            type t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
            val new: Config.t -> t
            val postBind: t * {var: Sxml.Var.t,
                               bind: Bind.t}-> t
            val descend: t * {var: Sxml.Var.t,
                              exp: Sxml.PrimExp.t,
                              subExp: SubExp.t} -> t
         end
      structure Addr:
         sig
            type t = Bind.addr

            val alloc: {var: Sxml.Var.t,
                        bind: Bind.t,
                        inst: Inst.t} -> t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
            val store: {empty: t -> 'a} -> 
                        {get: t -> 'a,
                         destroy: unit -> unit}
         end
end
