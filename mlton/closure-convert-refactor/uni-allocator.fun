functor UniAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

structure Addr =
struct
   type t = unit
   fun layout () = Layout.str "()"
   fun equals _ = true
   fun hash () = 0w1
end
structure Inst =
struct
   type t = unit
   fun layout () = Layout.str "()"
   fun equals _ = true
end
structure Config = 
struct
   type t = unit
end


fun alloc _ = ()
fun new _ = ()
fun preEval ((), _) = ()
fun postBind (inst, _) = inst
fun store {empty: unit -> 'a} =
   let
      val store = ref (empty ())
   in
      {get = fn () => !store,
       coalesce = fn _ => ((), !store)::[],
       destroy = fn _ => ()
      }
   end
val scan = Parse.<$ ((), Parse.str "uni")
end
