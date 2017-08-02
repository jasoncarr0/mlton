(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor UniAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

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
   fun preEval ((), _) = ()
   fun postBind (inst, _) = inst
end
structure Addr =
struct
   type t = unit
   fun alloc _ = ()
   fun realloc _ = ()
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
