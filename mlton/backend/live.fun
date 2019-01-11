(* Copyright (C) 2017 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *

 * This pass is based on the liveness algorithm described in section 4.13,
 * page 132, of Morgan's "Building an Optimizing Compiler".  BTW, the Dragon
 * book and Muchnick's book provided no help at all on speeding up liveness.
 * They suggest using bit-vectors, which is infeasible for MLton due to the
 * large size of and number of variables in SSA functions.
 *
 * Here is a description of the algorithm.
 *
 * Walk over the whole program and
 * 1. Build the predecessor graph of basic blocks.  Each basic block records the
 *    set of its predecessors and the set of variables live at the beginning of
 *    the block.
 * 2. For each variable record the block in which is defined and the list of
 *    blocks where it is used.
 *
 * Now, for each variable, propagate the liveness information backwards from uses
 * along basic blocks until the definition block is reached.
 *
 * That's it.  The reason why it's so fast is that it processes one variable at a
 * time, and hence the operation to determine if that variable is in the live
 * list for a particular block is constant time -- the variable is either at the
 * head of the list or it's not there.
 *)
functor Live (S: LIVE_STRUCTS): LIVE = 
struct

open S
open Rssa
datatype z = datatype Statement.t
datatype z = datatype Transfer.t

structure LiveInfo =
   struct
      datatype t = T of {block: Block.t,
                         live: (Var.t * Liveness.t) Buffer.t,
                         liveHS: {handler: Label.t option ref,
                                  link: unit option ref},
                         name: string,
                         preds: t list ref}

      fun layout (T {name, ...}) = Layout.str name

      fun new (name: string, block: Block.t) =
         T {block = block,
            live = Buffer.new {dummy = (Var.bogus, Liveness.bogus)},
            liveHS = {handler = ref NONE,
                      link = ref NONE},
            name = name,
            preds = ref []}

      fun live (T {live, ...}) = Buffer.toVector live

      fun liveHS (T {liveHS = {handler, link}, ...}) =
         {handler = !handler,
          link = isSome (!link)}

      fun equals (T {preds = r, ...}, T {preds = r', ...}) = r = r'

      fun addEdge (b, T {preds, ...}) =
         if List.exists (!preds, fn b' => equals (b, b'))
            then ()
         else List.push (preds, b)

      val addEdge =
         Trace.trace2 
         ("Live.LiveInfo.addEdge", layout, layout, Unit.layout) 
         addEdge
   end

val traceConsider = 
   Trace.trace3 ("Live.consider", LiveInfo.layout, Liveness.layout, LiveInfo.layout, Bool.layout)

fun live (function,
   {definedVar: {block: Block.t, var:Var.t} -> Liveness.t, flowBack, shouldConsider: Var.t -> bool, usedVar}) =
   let
      val shouldConsider =
         Trace.trace ("Live.shouldConsider", Var.layout, Bool.layout)
         shouldConsider
      val {args, blocks, ...} = Function.dest function
      val _ =
         Control.diagnostic
         (fn () =>
          let
             val numVars = ref 0
             fun loopVar (x, _) =
                if shouldConsider x
                   then Int.inc numVars
                else ()
             fun loopFormals v = Vector.foreach (v, loopVar)
             val () =
                Vector.foreach
                (blocks, fn Block.T {args, statements, transfer, ...} =>
                 (loopFormals args
                  ; Vector.foreach (statements, fn s =>
                                    Statement.foreachDef (s, loopVar))
                  ; Transfer.foreachDef (transfer, loopVar)))
             open Layout
          in
             align [seq [str "Live info for ",
                         Func.layout (Function.name function)],
                    seq [str "  num blocks ", Int.layout (Vector.length blocks)],
                    seq [str "  num vars ", Int.layout (!numVars)]]
          end)
      val {get = labelInfo: Label.t -> {argInfo: LiveInfo.t,
                                        block: Block.t,
                                        bodyInfo: LiveInfo.t},
           rem = removeLabelInfo,
           set = setLabelInfo, ...} =
         Property.getSetOnce (Label.plist,
                              Property.initRaise ("live info", Label.layout))
      val {get = varInfo: Var.t -> {defined: LiveInfo.t option ref,
                                    used: LiveInfo.t list ref},
           rem = removeVarInfo, ...} =
         Property.get (Var.plist,
                       Property.initFun (fn _ => {defined = ref NONE,
                                                  used = ref []}))
      datatype 'a defuse = Def of LiveInfo.t | Use of 'a * LiveInfo.t
      val handlerCodeDefUses: Label.t defuse list ref = ref []
      val handlerLinkDefUses: unit defuse list ref = ref []
      val allVars: Var.t list ref = ref []
      fun setDefined (x: Var.t, defined): unit =
         if shouldConsider x
            then (List.push (allVars, x)
                  ; #defined (varInfo x) := SOME defined)
         else ()
      val setDefined =
         Trace.trace2 ("Live.setDefined",
                       Var.layout, LiveInfo.layout, Unit.layout)
         setDefined
      (* Set the labelInfo for each block. *)
      val _ =
         Vector.foreach
         (blocks, fn block as Block.T {args, label, ...} =>
          let
             val name = Label.toString label
             val (argInfo, bodyInfo) =
                case Vector.length args of
                   0 => let val b = LiveInfo.new (name ^ "a", block)
                        in (b, b)
                        end
                 | _ => let val b = LiveInfo.new (name ^ "b", block)
                            val b' = LiveInfo.new (name ^ "c", block)
                            val _ = LiveInfo.addEdge (b, b')
                        in (b, b')
                        end
          in
             setLabelInfo (label, {argInfo = argInfo,
                                   block = block,
                                   bodyInfo = bodyInfo})
          end)
      (* Add the control-flow edges and set the defines and uses for each
       * variable.
       *)
      val head = LiveInfo.new ("main", (#block o labelInfo o #start o Function.dest) function)
      val _ = Vector.foreach (args, fn (x, _) => setDefined (x, head))
      val _ =
         Vector.foreach
         (blocks,
          fn Block.T {args, kind, label, statements, transfer, ...} =>
          let
            val {argInfo, bodyInfo = b, ...} = labelInfo label
            val _ = Vector.foreach (args, fn (x, _) => setDefined (x, argInfo))
            fun goto l = LiveInfo.addEdge (b, #argInfo (labelInfo l))
            (* Make sure that a cont's live vars includes variables live in its
             * handler.
             *)
            val _ =
               case kind of
                  Kind.Cont {handler, ...} =>
                     Handler.foreachLabel (handler, goto)
                | _ => ()
            fun define (x: Var.t): unit = setDefined (x, b)
            fun use (x: Var.t): unit =
               if shouldConsider x
                  then
                     let val {used, ...} = varInfo x
                     in
                        if (case !used of
                               [] => false
                             | b' :: _ => LiveInfo.equals (b, b'))
                           then ()
                        else List.push (used, b)
                     end
               else ()
            val use = Trace.trace ("Live.use", Var.layout, Unit.layout) use
            val _ =
               Vector.foreach
               (statements, fn s =>
                let
                   val _ = Statement.foreachDefUse (s, {def = define o #1,
                                                        use = use})
                   val _ =
                      case s of
                         SetExnStackSlot =>
                            List.push (handlerLinkDefUses, Use ((), b))
                       | SetHandler _ =>
                            List.push (handlerCodeDefUses, Def b)
                       | SetSlotExnStack =>
                            List.push (handlerLinkDefUses, Def b)
                       | _ => ()
                in
                   ()
                end)
            fun label l =
               let
                  val {block = Block.T {kind, ...}, ...} = labelInfo l
               in
                  case kind of
                     Kind.Handler =>
                        List.push (handlerCodeDefUses, Use (l, b))
                   | _ => goto l
               end
            val _ =
               Transfer.foreachDefLabelUse (transfer, {def = define o #1,
                                                       label = label,
                                                       use = use})
          in ()
          end)
      (* Back-propagate every variable from uses to define point. *)
      fun processVar (x: Var.t): unit =
         if not (shouldConsider x)
            then ()
         else
            let
               val {defined, used, ...} = varInfo x
               val defined = valOf (!defined)
               val todo: (LiveInfo.t * Liveness.t) list ref = ref []
               val _ = List.foreach (!used, fn (b as LiveInfo.T {block, live, ...}) =>
                  let
                     val lv = usedVar {block=block, var=x}
                  in
                     if not (LiveInfo.equals (defined, b))
                     then
                        ((Buffer.add (live, (x, lv))) ;
                        (List.push (todo, (b, lv))))
                     else ()
                  end)
               fun consider (from as LiveInfo.T {block=fromBlock, ...},
                             fromVal,
                             to as LiveInfo.T {block=toBlock, live, ...}) =
                  if LiveInfo.equals (defined, to)
                     then false
                  else
                     let
                        val last =
                           case Buffer.last live of
                                SOME (x', l) => if Var.equals (x, x') then SOME l else NONE
                              | NONE => NONE
                        val newVal =
                                 flowBack {earlier=toBlock, later=fromBlock,
                                           flowed=fromVal, present=last,
                                           var=x}
                     in
                        case last of
                             NONE => ( Buffer.add (live, (x, newVal))
                                     ; List.push (todo, (to, newVal))
                                     ; true)
                           | SOME l => if Liveness.equals (newVal, l)
                                          then false
                                       else
                                          (Buffer.setTop (live, (x, newVal))
                                          ; List.push (todo, (to, newVal))
                                          ; true)
                     end
               val consider = traceConsider consider
               fun loop () =
                  case !todo of
                     [] => ()
                   | (from as LiveInfo.T {preds, ...}, fromVal) :: bs =>
                        (todo := bs
                         ; List.foreach (!preds, fn to => ignore (consider (from, fromVal, to)))
                         ; loop ())
               val _ = loop ()
            in
               ()
            end
      val processVar =
         Trace.trace ("Live.processVar", Var.layout, Unit.layout) processVar
      val _ = List.foreach (!allVars, processVar)
      val _ = Function.foreachDef (function, fn (x, _) => removeVarInfo x)
      (* handler code and link slots are harder; in particular, they don't
       * satisfy the SSA invariant -- there are multiple definitions;
       * furthermore, a def and use in a block does not mean that the def 
       * occurs before the use.  But, a back propagated use will always
       * come after a def in the same block
       *)
      fun handlerLink (defuse: 'a defuse list ref,
                       sel: {handler: Label.t option ref,
                             link: unit option ref} -> 'a option ref) =
         let
            val todo: ('a * LiveInfo.t) list ref = ref []
            (* The foldr is important because the statements in each block were
             * visited in order, meaning that the earlier statements appear
             * later in !defuse.  Hence, with the foldr, the defs and uses are
             * visited in order for each block.
             *)
            val defs =
               List.foldr
               (!defuse, [], fn (du, defs) =>
                case du of
                   Def b => b::defs
                 | Use (a, b as LiveInfo.T {liveHS, ...}) =>
                      let
                         val _ =
                            if
                               (* Since we are visiting all of the statements
                                * in the block together, in order, we are
                                * guaranteed that if there is a prior definition
                                * then it will be first on defs.
                                *)
                               (case defs of 
                                   [] => false
                                 | b' :: _ => LiveInfo.equals (b, b'))
                               then ()
                            else (sel liveHS := SOME a
                                  ; List.push (todo, (a, b)))
                      in
                         defs
                      end)
            fun consider (b as LiveInfo.T {liveHS, ...}, a: 'a) =
               if List.exists (defs, fn b' => LiveInfo.equals (b, b'))
                  orelse isSome (!(sel liveHS))
                  then ()
               else (sel liveHS := SOME a
                     ; List.push (todo, (a, b)))
            fun loop () =
               case !todo of
                  [] => ()
                | (a, LiveInfo.T {preds, ...}) :: bs =>
                     (todo := bs
                      ; List.foreach (!preds, fn b => consider (b, a))
                      ; loop ())
            val _ = loop ()
         in
            ()
         end
      val _ = handlerLink (handlerCodeDefUses, #handler)
      val _ = handlerLink (handlerLinkDefUses, #link)
      val {get = labelLive, rem = remLabelLive, ...} =
         Property.get
         (Label.plist,
          Property.initFun
          (fn l =>
           let
              val {bodyInfo, argInfo, ...} = labelInfo l
              val () = removeLabelInfo l
              val {handler, link} = LiveInfo.liveHS bodyInfo

           in
              {begin = LiveInfo.live bodyInfo,
               beginNoFormals = LiveInfo.live argInfo,
               handler = handler,
               link = link}
           end))
      val () = Vector.foreach (blocks, fn b =>
                               ignore (labelLive (Block.label b)))
      val _ =
         Control.diagnostics
         (fn display =>
          let open Layout
          in
             Vector.foreach
             (blocks, fn b =>
              let
                 val l = Block.label b
                 val layoutBegin = Vector.layout (Layout.tuple2 (Var.layout, Liveness.layout))
                 val {begin, beginNoFormals, handler, link} = labelLive l
              in
                 display
                 (seq [Label.layout l,
                       str " ",
                       record [("begin", layoutBegin begin),
                               ("beginNoFormals", layoutBegin beginNoFormals),
                               ("handler", Option.layout Label.layout handler),
                               ("link", Bool.layout link)]])
              end)
          end)
   in 
      {labelLive = labelLive,
       remLabelLive = remLabelLive}
   end

val live =
   Trace.trace2 ("Live.live", Func.layout o Function.name, Layout.ignore,
                 Layout.ignore)
   live

end
