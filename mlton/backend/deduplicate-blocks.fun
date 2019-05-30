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


fun transformFunction main func =
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


      fun mkSupply (init, next) =
         let
            val arr = ResizableArray.empty ()
            val _ = ResizableArray.addToEnd (arr, init)
            fun get i =
               case ResizableArray.subOption (arr, i) of
                    SOME x => x
                  | NONE =>
                       (ResizableArray.addToEnd
                          (arr, next (ResizableArray.last arr)) ;
                        get i)

            fun set (i, x) =
               let
                  (* ensure length *)
                  val _ = get i
               in
                  ResizableArray.update (arr, i, x)
               end
         in
            {get=get, set=set, arr=arr}
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
      val {get=varSupply, ...} = mkSupply (Var.newString "xx", Var.new)
      val {get=labelSupply, ...} = mkSupply (Label.newString "LL", Label.new)

      val labels = Buffer.new {dummy=Label.bogus}
      val _ = Vector.foreach (blocks,
         fn b as Block.T {label, ...} =>
            let
               val id = Buffer.length labels
               val _ = Buffer.add (labels, label)
            in
               setLabelInfo (label, {block=b, id=id})
            end)
      val labels = Buffer.toVector labels

      val vars = Buffer.new {dummy=Var.bogus}
      fun getId v =
         let
            val i = Buffer.length vars
            val _ = Buffer.add (vars, v)
         in
            i
         end
      val {get=varInfo, set=setVarInfo, destroy=destVarInfo} =
         Property.destGetSet (Var.plist,
            Property.initRaise ("DeduplicateBlocks.transform.varInfo", Var.layout))
      val _ = Function.foreachDef (func,
         fn (v, _) => setVarInfo (v, {id=getId v}))

      (* globals have an id as they may be distinct,
       * but avoiding including them is important for performance *)
      val r = ref (Buffer.length vars)
      fun getId () =
         let
            val i = !r
            val _ = Int.inc r
         in
            i
         end
      val _ = Function.foreachDef (main,
         fn (v, _) => setVarInfo (v, {id=getId ()}))

      val numVars = !r
      val vars = Buffer.toVector vars

      (* Create reverse sets of destinations -> source sets *)

      (* Each label points to the labels it transfers to, in order *)
      val transfersTo = Vector.tabulate (Vector.length labels,
         fn _ => mkSupply (Set.empty, fn _ => Set.empty))
      (* Each label points to the variables it uses, in order *)
      val varUses = Vector.tabulate (Vector.length vars,
         fn _ => mkSupply (Set.empty, fn _ => Set.empty))
      (* Each variable points to its definition site *)
      val varDefs = Array.new (Vector.length labels, Element.Label ~1)

      val equivClasses = HashTable.new {hash=Block.hash, equals=Block.equals}
      val _ = Vector.foreach (blocks,
         fn b as Block.T {args, kind, label, statements, transfer} =>
            let
               val b =
                  let
                     val newStatements = ref []
                     val newTransfer = ref transfer
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
                           | _ => newTransfer := transfer)
                  in
                     case transfer of
                          Transfer.Goto _ =>
                              (appendStatements (statements, transfer) ;
                              Block.T {args=args, kind=kind, label=label,
                                       statements=(Vector.fromListRev (!newStatements)),
                                       transfer=(!newTransfer)})
                        | _ => b
                  end

               val {id, ...} = labelInfo label
               val _ = Block.foreachDef (b,
                  fn (v, _) =>
                     let
                        val {id=varId, ...} = varInfo v
                     in
                        Array.update (varDefs, varId, Element.Label id)
                     end)

               val (swapLabel, blabels) = mkSwap {supply=labelSupply, hash=Label.hash, equals=Label.equals}
               val (swapVar, bvars) = mkSwap {supply=varSupply, hash=Var.hash, equals=Var.equals}

               val b = Block.replaceLabels (b, swapLabel)
               val b = Block.replaceVars (b,
                  fn (v, t) => (swapVar v, t))

               val _ = List.foreachi (!blabels,
                  fn (j, l') =>
                     let
                        val {id, ...} = labelInfo l'
                        val {get, set, ...} = Vector.sub (transfersTo, id)
                     in
                        set (j, Set.add (get j, Element.Label id))
                     end)
               val _ = List.foreachi (!bvars,
                  fn (j, v) =>
                     let
                        val {id, ...} = varInfo v
                        val {get, set, ...} = Vector.sub (varUses, id)
                     in
                        set (j, Set.add (get j, Element.Label id))
                     end)

               val _ = HashTable.insertIfNew (equivClasses, b,
                  fn () => ref (Set.singleton (Element.Label id)),
                  fn s => s := Set.add (!s, Element.Label id))
            in
               ()
            end)
      val labelSets = List.map (HashTable.toList equivClasses, ! o #2)
      val numShapeClasses =
         HashTable.size equivClasses

      (* FIXME, globals must all be distinct *)
      val partition = Set.fromList (Vector.toListMap (vars, Element.Var o #id o varInfo))
         :: labelSets

      fun transitionsTo s =
         let
            val {get=labels, set=setLabels, arr=blabels} = mkSupply (Set.empty, fn _ => Set.empty)
            val {get=uses, set=setUses, arr=bvars} = mkSupply (Set.empty, fn _ => Set.empty)
            val defs = ref Set.empty
            val _ =
               Set.foreach (s,
                  fn x =>
                     case x of
                          Element.Var vi =>
                             let
                                val defLabel = Array.sub (varDefs, vi)
                                val _ = defs := Set.add (!defs, defLabel)
                                val {arr=uselabels, ...} = Vector.sub (varUses, vi)
                                val _ = ResizableArray.foreachi (uselabels,
                                    fn (j, ls) =>
                                       setUses (j, Set.union (ls, uses j)))
                              in
                                 ()
                             end
                        | Element.Label li =>
                             let
                                val {arr=labelTransitions, ...} = Vector.sub (transfersTo, li)
                                val _ = ResizableArray.foreachi (labelTransitions,
                                    fn (j, ls) =>
                                       setLabels (j, Set.union (ls, labels j)))
                              in
                                 ()
                             end)
         in
            List.concat [[!defs],
               ResizableArray.toList blabels,
               ResizableArray.toList bvars]
         end

      fun info init =
         let
            val vInfo = Array.tabulate (numVars, fn _ => init ())
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


fun transform (program as Program.T {functions, main, ...}) =
   let
      val functions = List.map (functions, transformFunction main)
   in
      program
   end
end
