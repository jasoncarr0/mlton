(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

structure Config = 
struct
   type t = int
   val scan = Parse.*> (Parse.str "m:", Parse.uint)
end
structure Bind =
struct
   type addr = (Sxml.Var.t * Sxml.Var.t list)
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
structure Inst =
struct
   type t = Sxml.Var.t list
   fun equals (c1, c2) =
      List.equals(c1, c2, Sxml.Var.equals)
   fun hash c = List.fold(c, 0w1, fn (arg, last) =>
      Sxml.Var.hash arg + 0w17 * last)
   fun layout c = Layout.list (List.map(c, Sxml.Var.layout))
end
structure Addr =
struct
   type t = (Sxml.Var.t * Sxml.Var.t list)
   fun equals ((v1, c1), (v2, c2)) = 
      Sxml.Var.equals (v1, v2) andalso
      List.equals(c1, c2, Sxml.Var.equals)
   fun hash (v, c) = Sxml.Var.hash v + 0w17 *
      List.fold(c, 0w1, fn (arg, last) =>
         Sxml.Var.hash arg + 0w17 * last)
   fun layout (_, c) = Layout.list (List.map(c, Sxml.Var.layout))

end

fun allocator m =
   let
      fun newInst () = []
      fun descend (ctxt, {var, exp=_, subExp}) = case subExp of
            SubExp.LambdaBody _ =>
               List.firstN (var :: ctxt, m) handle
                  _ => var :: ctxt
          | _ => ctxt
      fun postBind (inst, _) = inst
      fun alloc {var, bind=_, inst} = (var, inst)
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
   in
      {descend=descend, newInst=newInst, postBind=postBind,
       alloc=alloc, store=store}
   end


end
