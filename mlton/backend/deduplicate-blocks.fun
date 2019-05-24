(* Copyright (C) 2019 Jason Carr
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DeduplicateBlocks (S: RSSA_TRANSFORM_STRUCTS): RSSA_TRANSFORM = 
struct

open S
open Rssa

structure Element = struct
   datatype t =
      Var of int
    | Label of int

   fun compare (e1, e2) =
      case (e1, e2) of
            (Var v1, Var v2) => Int.compare (v1, v2)
          | (Var _, Label _) => Relation.LESS
          | (Label l1, Label l2) => Int.compare (l1, l2)
          | (Label _, Var _) => Relation.GREATER
end

structure Set = OrderedUniqueSet(
   struct
      type t = Element.t
      val compare = Element.compare
      fun equals (e1, e2) = Relation.EQUAL = Element.compare (e1, e2)
      fun op < (e1, e2) = compare (e1, e2) = Relation.LESS
      fun op <= (e1, e2) = compare (e1, e2) <> Relation.GREATER
      fun op > (e1, e2) = compare (e1, e2) = Relation.GREATER
      fun op >= (e1, e2) = compare (e1, e2) <> Relation.LESS
      fun max (e1, e2) = case compare (e1, e2) of
                              Relation.LESS => e2
                            | _ => e1
      fun min (e1, e2) = case compare (e1, e2) of
                              Relation.LESS => e1
                            | _ => e2
      fun layout e =
         Layout.seq (
         case e of
              Element.Var v => [Layout.str "Var ", Layout.str (Int.toString v)]
            | Element.Label l => [Layout.str "Label ", Layout.str (Int.toString l)])
   end)

structure Hopcroft = Hopcroft(structure Set = Set)


fun transformFunction func =
   let
      (* The gist of the algorithm is as follows:
       * for each block in the function, we collect the variables and labels
       * that appear in that block in order, replacing them with a canonical version.
       *
       * We also act as though any Gotos are inlined, appending them onto the current block,
       * so that we're not as easily foiled by different inlining decisions.
       *
       * We'll place them into obviously distinct classes, then solve a greatest
       * fixed point of references to each other using Hopcroft's DFA minimization algorithm.
       *
       * Now, each block of the same shape is the same form, so we can unify them
       * purely based on Block.hash and Block.equals. So we place blocks which
       * are the same shape into the same class in the initial partition, since
       * these blocks are not distinguishable on their own.
       * All variables are placed in the same initial partition.
       *
       * Now, we construct an automaton over these labels/vars with edges:
       * def: from each var to its definition label
       * label1..n : from each label to unique label appearing in it
       * var1..n : each var use and def within a block
       *    (remember that blocks with different shapes are always different,
       *    so it's okay to conflate label/vars from diffent shapes)
       *
       * As it happens, we don't need to care about recursion or local definitions
       * since these will simply turn into loops for which distinguishability
       * will suffice.
       *
       * At this point Hopcroft's algorithm produces a minimal partition
       * of distinguishable labels. We simply choose one from each class and
       * map all occurences to that label. A bias towards smaller true size
       * picks those which likely have more code shared (or else they'll get
       * their destination inlined anyway)
       *)
      val {blocks, ...} = Function.dest func
      val {get=labelInfo, set=setLabelInfo, destroy=destLabelInfo} =
         Property.destGetSet (Label.plist,
            Property.initRaise ("DeduplicateBlocks.transform.labelBlock", Label.layout))
      val _ = Vector.foreach (blocks,
         fn b as Block.T {label, ...} =>
            setLabelInfo (label, {block=b, blabels=[], bvars=[], id= ~1}))


      fun mkSupply (init, next) =
         let
            val arr = ResizableArray.empty ()
            val _ = ResizableArray.addToEnd (arr, init)
            fun getI i =
               case ResizableArray.subOption (arr, i) of
                    SOME x => x
                  | NONE =>
                       (ResizableArray.addToEnd
                          (arr, next (ResizableArray.last arr)) ;
                        getI i)

         in
            (getI, arr)
         end
      fun mkSwap {supply, hash, equals} =
         let
            val table = HashTable.newOfSize {hash=hash, equals=equals, size=16}
            val xs = ref []
            val i = ref 0
         in
            (fn orig => HashTable.lookupOrInsert
               (table, orig, fn () =>
                  let
                     val x = supply (!i)
                     val _ = Int.inc i
                     val _ = List.push (xs, orig)
                  in
                     x
                  end), xs)
         end
      val (varSupply, _) = mkSupply (Var.newString "xx", Var.new)
      val (labelSupply, _) = mkSupply (Label.newString "LL", Label.new)


      val equivClasses = HashTable.new {hash=Block.hash, equals=Block.equals}
      val labels = Buffer.new {dummy=Label.bogus}

      val _ = Vector.foreach (blocks,
         fn b as Block.T {args, kind, label, statements, transfer} =>
            let
               val b =
                  let
                     val newStatements = ref []
                     val replace = HashTable.new {hash=Var.hash, equals=Var.equals}
                     (* TODO: make sure to switch the transfer to the destination transfer *)
                     fun appendStatements (statements, transfer) =
                        (Vector.foreach (statements,
                           fn st => List.push (newStatements, st)) ;
                        case transfer of
                             Transfer.Goto {args=gotoArgs, dst} =>
                                 (case (#block o labelInfo) dst of
                                      Block.T {args=dstArgs, statements, transfer, ...} =>
                                       (Vector.foreach2 (dstArgs, gotoArgs, fn ((dstv, _), v) =>
                                          ignore (HashTable.lookupOrInsert
                                             (replace, dstv, fn () => v))) ;
                                       appendStatements (statements, transfer)))
                           | _ => ())
                  in
                     case transfer of
                          Transfer.Goto _ =>
                              (appendStatements (statements, transfer) ;
                              Block.T {args=args, kind=kind, label=label,
                                       statements=(Vector.fromListRev (!newStatements)),
                                       transfer=transfer})
                        | _ => b
                  end

               val (swapLabel, blabels) = mkSwap {supply=labelSupply, hash=Label.hash, equals=Label.equals}
               val (swapVar, bvars) = mkSwap {supply=varSupply, hash=Var.hash, equals=Var.equals}
               val b = Block.replaceLabels (b, swapLabel)
               val b = Block.replaceVars (b,
                  fn (v, t) => (swapVar v, t))
               (* label still refers to the original label, before swapping *)
               val id = Buffer.length labels

               val _ = Buffer.add (labels, label)
               val _ = HashTable.insertIfNew (equivClasses, b,
                  fn () => ref (Set.singleton (Element.Label id)),
                  fn s => s := Set.add (!s, Element.Label id))
               val {block, ...} = labelInfo label
               val blabels = !blabels
               val bvars = !bvars
               val _ = setLabelInfo (label, {block=block, blabels=blabels, bvars=bvars, id=id})
            in
               ()
            end)

      val labels = Buffer.toVector labels
      val labelSets = List.map (HashTable.toList equivClasses, ! o #2)

      val vars = Buffer.new {dummy=Var.bogus}
      fun getId v =
         let
            val i = Buffer.length vars
            val _ = Buffer.add (vars, v)
         in
            i
         end
      val {get=varInfo, set=setVarInfo, destroy=destVarInfo} =
         Property.destGetSetOnce (Var.plist,
            Property.initRaise ("DeduplicateBlocks.transform.varInfo", Var.layout))
      val {args, blocks, start, ...} = Function.dest func
      val _ = Vector.foreach (args,
         fn (v, _) => setVarInfo (v, {def=start, id=getId v}))
      val _ = Vector.foreach (blocks,
         fn Block.T {args, statements, label, ...} =>
            (Vector.foreach (args, fn (v, _) => setVarInfo (v, {def=label, id=getId v})) ;
             Vector.foreach (statements,
               fn s => Statement.foreachDef (s,
                  fn (v, _) => setVarInfo (v, {def=label, id=getId v})))))
      val vars = Buffer.toVector vars

      val partition = Set.fromList (List.tabulate (Vector.length vars, fn i => Element.Var i))
         :: labelSets


      (* Now we precompute a table of distinct transitions for each var and label
       * There is always one def character in the alphabet for var -> label
       * and each label has a list of labels and vars it depends on *)

      val labelTransitions =
         Vector.map (labels,
            fn l =>
               let
                  val {blabels, bvars, ...} = labelInfo l
                  val labelIds = List.map (blabels, Element.Label o #id o labelInfo)
                  val varIds = List.map (bvars, Element.Var o #id o varInfo)
               in
                  (labelIds, varIds)
               end)
      val varTransition = Vector.map (vars, Element.Var o #id o labelInfo o #def o varInfo)

      fun transitionsTo s =
         let
            val (labelsI, blabels) = mkSupply (ref Set.empty, fn _ => ref Set.empty)
            val (varsI, bvars) = mkSupply (ref Set.empty, fn _ => ref Set.empty)
            val def = ref Set.empty
            val _ =
               Set.foreach (s,
                  fn x =>
                     case x of
                          Element.Var vi =>
                              def := Set.add (!def, Vector.sub (varTransition, vi))
                        | Element.Label li =>
                             let
                                val (labelIds, varIds) = Vector.sub (labelTransitions, li)
                                val _ = List.foreachi (labelIds,
                                    fn (ix, lid) => labelsI ix := Set.add (!(labelsI ix), lid))
                                val _ = List.foreachi (varIds,
                                    fn (ix, vid) => varsI ix := Set.add (!(varsI ix), vid))
                              in
                                 ()
                             end)
         in
            List.concat [[!def],
               ResizableArray.toListMap (blabels, !),
               ResizableArray.toListMap (bvars, !)]
         end

      fun info init =
         let
            val vInfo = Array.tabulate (Vector.length vars, fn _ => init ())
            val lInfo = Array.tabulate (Vector.length labels, fn _ => init ())
            fun mkRef (arr, i) =
               {get=fn () => Array.sub (arr, i),
                set=fn u => Array.update (arr, i, u)}
         in
            fn Element.Var vi => mkRef (vInfo, vi)
             | Element.Label li => mkRef (lInfo, li)
         end

      val partition = Hopcroft.run
         {initialPartition=partition,
          transitionsTo=transitionsTo,
          info=info}

      val _ = Control.diagnostic (fn () =>
         let
            open Layout
            val numBlockClasses =
               (List.length (List.keepAll (partition, fn s =>
                  Set.exists (s, fn e => case e of Element.Label _ => true | _ => false))))
            val numShapeClasses =
               HashTable.size equivClasses
            val numBlocks = Vector.length blocks
         in
            mayAlign
            [seq [str "Function: ", Func.layout (Function.name func)],
             seq [str "Initial: ", Int.layout numBlocks],
             seq [str "Shapes: ", Int.layout numShapeClasses],
             seq [str "Unique: ", Int.layout numBlockClasses]]
         end)

      val _ = destVarInfo ()
      val _ = destLabelInfo ()
   in
      func
   end


fun transform (program as Program.T {functions, ...}) =
   let
      val functions = List.map (functions, transformFunction)
   in
      program
   end
end
