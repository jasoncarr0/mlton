(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor HashAllocator(S: ALLOCATOR_STRUCTS):ALLOCATOR = 
struct
open S

fun combine (hsh1, hsh2) = 
   hsh1 * 0w11 + hsh2 * 0w7 + 0wx9e3779b9 
   (* = a * 11 + b * 7 + golden ratio *)

structure Config = 
struct
   type t = word
   val scan = Parse.*> (Parse.str "hash:", Parse.<$> (Word.fromInt, Parse.uint))
end
structure Bind =
struct
   type addr = word
   datatype t = AppArg of (Sxml.Var.t * Sxml.Lambda.t * addr)
              | AppFree of (Sxml.Var.t * Sxml.Lambda.t * addr)
              | CaseArg of Sxml.Con.t
              | ConArg of (Sxml.Con.t * addr)
              | HandleArg
              | LetVal of Sxml.PrimExp.t * Sxml.Type.t
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
   type t = word
   fun layout h = Layout.str (Word.toString h)
   val equals = op =
   fun hash h = h
end
structure Addr =
struct
   type t = word
   val layout = Layout.str o Word.toString
   val equals = op =
   fun hash x = x
   fun store {empty: word -> 'a} =
      let
         val set = HashSet.new {hash=fn (h, _) => h} 
         fun get h = 
            let 
               val (_, res) = HashSet.lookupOrInsert 
                  (set, h, fn (h', _) => h = h', fn () => (h, empty h))
            in
               res
            end
      in
         {get=get, destroy=fn () => ()}
      end
end

fun allocator max =
   let
      val m = Word.<< (0w1, max)
      fun new () = combine (0w0, m)
      fun descend (hsh, {var, exp=_, subExp=_}) =
         combine (0w13 + Sxml.Var.hash var, hsh)
      fun postBind (hsh, {var, bind=_}) = combine (Sxml.Var.hash var, hsh)
      fun alloc {var, bind=_, inst=hsh} = combine (Sxml.Var.hash var, hsh) mod m
   in
      {newInst=new, postBind=postBind, descend=descend,
       alloc=alloc, store=Addr.store}
   end

end
