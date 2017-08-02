(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor KAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

structure Config = 
struct
   type t = int
   val scan = Parse.*> (Parse.str "k:", Parse.uint)
end
structure Inst =
struct
   type t = (int * Sxml.Var.t list)
   fun equals ((_, c1), (_, c2)) =
      List.equals(c1, c2, Sxml.Var.equals)
   fun hash (_, c) = List.fold(c, 0w1, fn (arg, last) =>
      Sxml.Var.hash arg + 0w17 * last)
   fun layout (_, c) = Layout.list (List.map(c, Sxml.Var.layout))
   fun new k = (k,[])
   fun preEval ((k, ctxt), {var, exp}) = (case exp of
                  Sxml.PrimExp.App {func, ...} => let
                     in (k, List.firstN (var :: ctxt, k) handle
                        _ => var :: ctxt)
                     end
                | _ => (k, ctxt))
   fun postBind (inst, _) = inst
end
structure Addr =
struct
   type t = (Sxml.Var.t * Sxml.Var.t list)
   fun alloc (var, (_, ctxt)) = (var, ctxt) (* discard k *)
   fun equals ((v1, c1), (v2, c2)) = 
      Sxml.Var.equals (v1, v2) andalso
      List.equals(c1, c2, Sxml.Var.equals)
   fun hash (v, c) = Sxml.Var.hash v + 0w17 *
      List.fold(c, 0w1, fn (arg, last) =>
         Sxml.Var.hash arg + 0w17 * last)
   fun layout (_, c) = Layout.list (List.map(c, Sxml.Var.layout))
   fun store {empty: (Sxml.Var.t * Sxml.Var.t list) -> 'a} =
      let
         val {get = getList: Sxml.Var.t -> (Sxml.Var.t list * 'a) list ref,
              destroy = destroy} =
                Property.destGet
                (Sxml.Var.plist,
                 Property.initFun (fn _ => ref []))
         fun get (var, ctxt) = 
            let
               val ctxts = getList var
            in
               case List.peek (!ctxts, 
                  fn (ctxt', _) => List.equals (ctxt, ctxt', Sxml.Var.equals)) of
                     SOME (_, v) => v
                   | NONE => let val v = empty (var, ctxt)
                        in List.push (ctxts, (ctxt, v)); v 
                     end
            end
      in
         {get=get, destroy=destroy}
      end

end

end
