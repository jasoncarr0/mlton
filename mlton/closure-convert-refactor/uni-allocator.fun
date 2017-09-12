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
   type addr = Sxml.Type.t
   datatype t = AppArg of Sxml.Var.t * Sxml.Lambda.t * addr
              | AppFree of Sxml.Var.t * Sxml.Lambda.t * addr
              | CaseArg of Sxml.Con.t * Sxml.Type.t
              | ConArg of Sxml.Con.t * addr
              | HandleArg of Sxml.Type.t
              | LetVal of Sxml.PrimExp.t * Sxml.Type.t
              | PrimAddr of Sxml.Type.t Sxml.Prim.t * Sxml.Type.t
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
   type t = Sxml.Type.t
   fun alloc {var=_, bind, inst=_} = case bind of
      Bind.AppArg (_, _, addr) => addr
    | Bind.AppFree (_, _, addr) => addr
    | Bind.CaseArg (_, ty) => ty
    | Bind.ConArg (_, addr) => addr
    | Bind.HandleArg ty => ty
    | Bind.LetVal (_, ty) => ty
    | Bind.PrimAddr (_, ty) => ty
   val equals = Sxml.Type.equals
   val hash = Sxml.Type.hash
   val layout = Sxml.Type.layout
   fun store {empty: t -> 'a} =
      let
         val {get: Sxml.Type.t -> ('a ref), destroy} =
                Property.destGet
                (Sxml.Type.plist,
                 Property.initFun (fn ty => ref (empty ty)))
      in
         {get= ! o get, destroy=destroy}
      end
end

fun allocator _ =
   {newInst=Inst.new, postBind=Inst.postBind, descend=Inst.descend,
    alloc=Addr.alloc, store=Addr.store}

end
