(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor Globalize (S: GLOBALIZE_STRUCTS): GLOBALIZE =
struct

open S
open Sxml

fun globalize {program: Program.t, freeVars} =
   let
      val Program.T {datatypes, body, ...} = program

      local
         val {get = tyconIsBig: Tycon.t -> bool,
              set = setTyconIsBig, destroy = destroyTyconIsBig} =
            Property.destGetSetOnce
            (Tycon.plist, Property.initConst false)
         fun makeTyconBig tycon = setTyconIsBig (tycon, true)
         val _ = (Vector.foreach (datatypes, makeTyconBig o #tycon);
                  makeTyconBig Tycon.array;
                  makeTyconBig Tycon.arrow;
                  makeTyconBig Tycon.vector)
      in
         val tyconIsBig = tyconIsBig
         val tyconIsSmall = not o tyconIsBig
         val destroyTyconIsBig = destroyTyconIsBig
      end
      fun typeIsSmall t =
         case Type.dest t of
            Type.Con (c, ts) =>
               tyconIsSmall c
               andalso if (Tycon.equals (c, Tycon.tuple)
                           orelse Tycon.equals (c, Tycon.reff))
                          then Vector.forall (ts, typeIsSmall)
                          else true
          | _ => Error.bug "Globalize.typeIsSmall: strange type"
      val typeIsSmall =
         Trace.trace ("Globalize.typeIsSmall", Type.layout, Bool.layout)
         typeIsSmall

      val hasThreadSwitchTo =
         Exp.hasPrim
         (body, fn p =>
          case Prim.name p of
             Prim.Name.Thread_switchTo => true
           | _ => false)

      val {get = varIsGlobal: Var.t -> bool,
           set = setVarIsGlobal, rem = remVarIsGlobal} =
         Property.getSetOnce
         (Var.plist, Property.initConst false)
      fun destroyVarIsGlobal () =
         Exp.foreachBoundVar
         (body, fn (x, _, _) => remVarIsGlobal x)
      fun makeVarGlobal x = setVarIsGlobal (x, true)
      val isGlobal = varIsGlobal o VarExp.var
      fun areGlobal xs = Vector.forall (xs, isGlobal)

      fun loopExp (exp: Exp.t, once: bool) =
         List.fold (Exp.decs exp, once, loopDec)
      and loopDec (dec: Dec.t, once: bool) =
         case dec of
            Dec.MonoVal {var, ty, exp} =>
               let
                  val (global, once) =
                     case exp of
                        PrimExp.App _ =>
                           (* If threads/conts are used, then the
                            * application might call
                            * Thread_copyCurrent, in which case,
                            * subsequent stuff might run many times.
                            *)
                           (false, once andalso not (hasThreadSwitchTo))
                      | PrimExp.Case {cases, default, ...} =>
                           let
                              val once' =
                                 Cases.fold
                                 (cases, once, fn (e, b) =>
                                  loopExp (e, once) andalso b)
                              val once' =
                                 Option.fold
                                 (default, once', fn ((e, _), b) =>
                                  loopExp (e, once) andalso b)
                           in
                              (false, once')
                           end
                      | PrimExp.ConApp {arg, ...} =>
                           (case arg of NONE => true | SOME x => isGlobal x, once)
                      | PrimExp.Const _ => (true, once)
                      | PrimExp.Handle {try, handler, ...} =>
                           (false, loopExp (handler, loopExp (try, once)))
                      | PrimExp.Lambda lam =>
                           (loopLambda lam;
                            (Vector.forall (freeVars lam, varIsGlobal), once))
                      | PrimExp.PrimApp {prim, args, ...} =>
                           let
                              val global =
                                 areGlobal args andalso
                                 ((Prim.isFunctional prim
                                   (* Don't want to move MLton_equal or MLton_hash
                                    * into the globals because polymorphic
                                    * equality and hasing isn't implemented
                                    * there.
                                    *)
                                   andalso
                                   (case Prim.name prim of
                                       Prim.Name.MLton_equal => false
                                     | Prim.Name.MLton_hash => false
                                     | _ => true))
                                  orelse
                                  (once andalso
                                   (case Prim.name prim of
                                       Prim.Name.Ref_ref => typeIsSmall ty
                                     | _ => false)))
                              val once =
                                 once andalso
                                 (case Prim.name prim of
                                     Prim.Name.Thread_copyCurrent => false
                                   | _ => true)
                           in
                              (global, once)
                           end
                      | PrimExp.Profile _ => (false, once)
                      | PrimExp.Raise _ => (false, once)
                      | PrimExp.Select {tuple, ...} => (isGlobal tuple, once)
                      | PrimExp.Tuple xs => (areGlobal xs, once)
                      | PrimExp.Var x => (isGlobal x, once)
                  val _ = if global then makeVarGlobal var else ()
               in
                  once
               end
          | Dec.Fun {decs, ...} =>
               (if Vector.isEmpty decs
                   then ()
                   else let
                           val {lambda, ...} = Vector.sub (decs, 0)
                        in
                           if Vector.forall (freeVars lambda, varIsGlobal)
                              then Vector.foreach (decs, makeVarGlobal o #var)
                              else ()
                        end;
                Vector.foreach (decs, loopLambda o #lambda);
                once)
          | _ => Error.bug "Globalize.loopDec: strange dec"
      and loopLambda (lambda: Lambda.t): unit =
         ignore (loopExp (Lambda.body lambda, false))

      val _ = loopExp (body, true)
      val _ = destroyTyconIsBig ()
   in
      {isGlobal = varIsGlobal,
       destroy = destroyVarIsGlobal}
   end

val globalize =
   Control.trace (Control.Pass, "globalize")
   globalize

end
