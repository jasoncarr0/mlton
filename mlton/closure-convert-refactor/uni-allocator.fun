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
   datatype t = LetVal of Sxml.PrimExp.t
              | AppArg of (Sxml.Lambda.t * addr)
              | AppFree of (Sxml.Lambda.t * addr)
              | ConArg of (Sxml.Con.t * addr)
              | CaseArg of Sxml.Con.t
              | HandleArg
end
structure SubExp =
struct
   datatype t = LambdaBody of Sxml.Lambda.t
              | CaseBody of (Sxml.Con.t * Sxml.Var.t option) option
              | HandleTry
              | HandleCatch
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


end
