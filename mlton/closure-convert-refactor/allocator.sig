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
            datatype t = AppArg of (Sxml.Lambda.t * addr)
                       | AppFree of (Sxml.Lambda.t * addr)
                       | CaseArg of Sxml.Con.t
                       | ConArg of (Sxml.Con.t * addr)
                       | HandleArg
                       | LetVal of Sxml.PrimExp.t
                       | PrimAddr of Sxml.Type.t Sxml.Prim.t
         end
      structure SubExp:
         sig
            datatype t = CaseBody of (Sxml.Con.t * Sxml.Var.t option) option
                       | HandleCatch
                       | HandleTry
                       | LambdaBody of Sxml.Lambda.t
         end
      structure Inst:
         sig
            type t
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
         end
      structure Addr:
         sig
            type t = Bind.addr
            val equals: t * t -> bool
            val hash: t -> word
            val layout: t -> Layout.t
         end
      val allocator: Config.t ->
            {newInst: unit -> Inst.t,
             postBind: Inst.t * {var: Sxml.Var.t,
                                 bind: Bind.t}-> Inst.t,
             descend: Inst.t * {var: Sxml.Var.t,
                                exp: Sxml.PrimExp.t,
                                subExp: SubExp.t} -> Inst.t,
             alloc: {var: Sxml.Var.t,
                     bind: Bind.t,
                     inst: Inst.t} -> Addr.t,
             store: {empty: Addr.t -> 'a} ->
                        {get: Addr.t -> 'a,
                         destroy: unit -> unit}}

end
