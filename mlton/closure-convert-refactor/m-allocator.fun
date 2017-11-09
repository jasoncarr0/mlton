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
   datatype conSetting = ConMCFA
                   | Con0CFA
                   | ConGlobal
   type t = {m: int, conSetting: conSetting}
   local
      open Parse
      infix 1 <|> >>=
      infix 2 <&>
      infix  3 <*> <* *>
      infixr 4 <$> <$$> <$$$> <$
   in
      fun mkCfg (m, conSetting) = {m=m, conSetting=conSetting}
      val parseConSetting = any
            [ConMCFA <$ str "mcfa",
             Con0CFA <$ str "0cfa",
             ConGlobal <$ str "global"]
      val scan = mkCfg <$$> (str "m:" *> uint,
      cut (str "," *> spaces *> str "con:" *> parseConSetting <|> pure ConMCFA))
   end
end
structure Bind =
struct
   type addr = (Sxml.Var.t * Sxml.Type.t * Sxml.Var.t list)
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
   type t = (Sxml.Var.t * Sxml.Type.t * Sxml.Var.t list)
   fun equals ((v1, _, c1), (v2, _, c2)) =
      Sxml.Var.equals (v1, v2) andalso
      List.equals(c1, c2, Sxml.Var.equals)
   fun hash (v, _, c) = Sxml.Var.hash v + 0w17 *
      List.fold(c, 0w1, fn (arg, last) =>
         Sxml.Var.hash arg + 0w17 * last)
   fun layout (v, _, c) = Layout.seq
      [Sxml.Var.layout v,
       Layout.str ":",
       Layout.list (List.map(c, Sxml.Var.layout))]

   fun getType (_, ty, _) = ty
end

fun allocator {m, conSetting} =
   let
      (* only used for ConGlobal setting *)
      val {get = conInfo: Sxml.Con.t -> Sxml.Type.t -> Addr.t,
           destroy = destroyConInfo} =
         Property.destGet
         (Sxml.Con.plist,
          Property.initFun (fn con => fn ty => (Sxml.Var.newString ("con_" ^ (Sxml.Con.toString con)), ty, [])))
      (* used when we want to collapse type information *)
      val {get = typeInfo: Sxml.Type.t -> Addr.t,
           destroy = destroyTypeInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (fn ty =>
            (Sxml.Var.newString ("type_" ^
            (Sxml.Tycon.toString (Sxml.Type.tycon ty))), ty, [])))
      (* used when we want to collapse type information *)


      fun extend (ctxt, var) =
         (List.firstN (var :: ctxt, m) handle
            _ => var :: ctxt)
      fun newInst () = []
      fun descend (ctxt, {var, exp=_, subExp}) = case subExp of
            SubExp.LambdaBody _ => extend (ctxt, var)
          | _ => ctxt
      fun postBind (inst, _) = inst
      fun alloc {var, bind, inst} = case bind of
          Bind.AppArg (call, _, (_, ty, ctxt0)) => (var, ty, extend (ctxt0, call))
        | Bind.AppFree (call, _, (_, ty, ctxt0)) => (var, ty, extend (ctxt0, call))
        | Bind.CaseArg (con, ty) => (case conSetting of
            Config.ConGlobal => conInfo con ty
          | Config.Con0CFA => (var, ty, [])
          | Config.ConMCFA => (var, ty, inst))
        | Bind.ConArg (con, (var', ty, ctxt)) => (case conSetting of
            Config.ConGlobal => conInfo con ty
          | Config.Con0CFA => (var', ty, []) (* delete argument context *)
          | Config.ConMCFA => (var', ty, ctxt)) (* keep original address *)
        | Bind.LetVal (exp, ty) => (case exp of
             Sxml.PrimExp.ConApp {arg, ...} =>
               (case (conSetting, arg) of
                   (Config.ConGlobal, _) => typeInfo ty
                 | (Config.Con0CFA, _) => (var, ty, [])
                 | (Config.ConMCFA, SOME _) => (var, ty, inst)
                 | (Config.ConMCFA, NONE) => (var, ty, inst))
           | Sxml.PrimExp.Const _ => typeInfo ty (* always a single proxy *)
           | _ => (var, ty, inst))
        | Bind.PrimAddr (_, ty) => (var, ty, []) (* always 0-cfa for refs *)
        | Bind.HandleArg ty => (case conSetting of
            Config.ConGlobal => typeInfo ty
          | Config.Con0CFA => (var, ty, [])
          | Config.ConMCFA => (var, ty, inst))

      fun destroy () = (destroyConInfo (); destroyTypeInfo ())
   in
      {descend=descend, newInst=newInst, postBind=postBind, alloc=alloc, destroy=destroy}
   end

   fun store (_, empty: (Sxml.Var.t * Sxml.Type.t * Sxml.Var.t list) -> 'a) =
      let
         val {get=getList: Sxml.Var.t -> (Sxml.Var.t list * 'a) list ref,
              destroy} =
                Property.destGet
                (Sxml.Var.plist,
                 Property.initFun (fn _ => ref []))
         fun get (var, ty, ctxt) =
            let
               val ctxts = getList var
            in
               case List.peek (!ctxts,
                  fn (ctxt', _) => List.equals (ctxt, ctxt', Sxml.Var.equals)) of
                     SOME (_, v) => v
                   | NONE => let val v = empty (var, ty, ctxt)
                        in List.push (ctxts, (ctxt, v)); v
                     end
            end
      in
         {get=get, destroy=destroy}
      end


end
