(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor UniAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

structure Bind =
struct
   type addr = unit
   datatype t = AppArg of (Sxml.Lambda.t * addr)
              | AppFree of (Sxml.Lambda.t * addr)
              | CaseArg of Sxml.Con.t
              | ConArg of (Sxml.Con.t * addr)
              | HandleArg
              | LetVal of Sxml.PrimExp.t
              | PrimAddr of Sxml.Type.t Sxml.Prim.t
end
structure SubExp =
struct
   datatype t = CaseBody of (Sxml.Con.t * Sxml.Var.t option) option
              | HandleCatch
              | HandleTry
              | LambdaBody of Sxml.Lambda.t
end
structure Config = 
struct
   type t = unit
   val scan = Parse.<$ ((), Parse.str "uni")
end
structure Inst =
struct
   type t = unit
   fun equals _ = true
   fun hash () = 0w1
   fun layout () = Layout.str "()"
   fun new _ = ()
   fun descend _ = ()
   fun postBind _ = ()
end
structure Addr =
struct
   type t = unit
   fun alloc _ = ()
   fun equals _ = true
   fun hash () = 0w1
   fun layout () = Layout.str "()"
   fun store {empty: unit -> 'a} =
      let
         val store = ref (empty ())
      in
         {get = fn () => !store,
          destroy = fn () => ()
         }
      end
end

fun allocator _ =
   {newInst=Inst.new, postBind=Inst.postBind, descend=Inst.descend,
    alloc=Addr.alloc, store=Addr.store}

end
