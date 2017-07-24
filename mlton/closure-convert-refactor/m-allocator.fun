functor MAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

structure Addr =
struct
   type t = (Sxml.Var.t * Sxml.Lambda.t list)
   fun layout _ = Layout.str "m-addr"
   fun equals ((v1, c1), (v2, c2)) = 
      Sxml.Var.equals (v1, v2) andalso
      List.equals(c1, c2, Sxml.Lambda.equals)   
end
structure Inst =
struct
   type t = (int * Sxml.Lambda.t list)
   fun layout _ = Layout.str "ctxt"
   fun equals ((m1, c1), (m2, c2)) =
      List.equals(c1, c2, Sxml.Lambda.equals)
end
structure Config = 
struct
   type t = int
end


fun alloc (var, (_, ctxt)) = (var, ctxt) (* discard m *)
fun equals ((_, ctxt), (_, ctxt')) = List.equals(ctxt, ctxt', Sxml.Lambda.equals)
fun new m = (m,[])
fun preEval ((m, ctxt), exp) = (case exp of
                  Sxml.PrimExp.Lambda lam => let
                     in (m, List.firstN (lam :: ctxt, m) handle
                        _ => lam :: ctxt)
                     end
                | _ => (m, ctxt))
fun layout (_, ctxt) = Layout.list (List.map(ctxt, Sxml.Lambda.layout))
fun postBind (inst, _) = inst
fun store {empty: (Sxml.Var.t * Sxml.Lambda.t list) -> 'a} =
   let
      val {get = getList: Sxml.Var.t -> (Sxml.Lambda.t list * 'a) list ref,
           rem = rem} =
             Property.get
             (Sxml.Var.plist,
              Property.initFun (fn _ => ref []))
      fun get (var, ctxt) = 
         let
            val ctxts = getList var
         in
            case List.peek (!ctxts, 
               fn (ctxt', _) => List.equals (ctxt, ctxt', Sxml.Lambda.equals)) of
                  SOME (_, v) => v
                | NONE => let val v = empty (var, ctxt)
                     in List.push (ctxts, (ctxt, v)); v 
                  end
         end
      fun coalesce var = List.map(!(getList var), fn (ctxt, v) => ((var, ctxt), v))
                          
   in
      {get=get, destroy=rem, coalesce=coalesce}
   end

val scan = Parse.*> (Parse.str "m:", Parse.uint)
end
