(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature LIVE_STRUCTS =
   sig
      structure Rssa: RSSA
      structure Liveness: sig
         type t

         val equals: t * t -> bool
         val layout: t -> Layout.t
         val bogus: t
      end
   end

signature LIVE =
   sig
      include LIVE_STRUCTS
      include RSSA

      val live:
         Function.t * {
               (* flow back to get a new liveness
                * if the new liveness changes, then process again *)
               flowBack: {earlier: Block.t,
                          later: Block.t,

                          flowed: Liveness.t,
                          present: Liveness.t,

                          var: Var.t} -> Liveness.t,
               usedVar: {block: Block.t,
                        var: Var.t} -> Liveness.t,
               definedVar: {block: Block.t,
                            var: Var.t} -> Liveness.t,
               shouldConsider: Var.t -> bool
            }
         -> {labelLive: Label.t
               -> { (* live at beginning of block. *)
                    begin: (Var.t * Liveness.t) vector,
                    (* variables live before block arguments are considered *)
                    beginNoFormals: (Var.t * Liveness.t) vector,
                    (* live handler slots at beginning of block. *)
                    handler: Label.t option,
                    link: bool
                    },
             remLabelLive: Label.t -> unit}
   end
