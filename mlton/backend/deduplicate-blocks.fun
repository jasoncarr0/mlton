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

structure Hopcroft = Hopcroft(
   struct
      structure Set = Set
   end)


fun transformFunction func =
   let
      val {get=varDef, set=setVarDef, destroy=destVarDef} =
         Property.destGetSetOnce (Var.plist,
            Property.initRaise ("DeduplicateBlocks.transform.varDef", Var.layout))
      val {args, blocks, start, ...} = Function.dest func
      val _ = Vector.foreach (args,
         fn (v, _) => setVarDef (v, start))
      val _ = Vector.foreach (blocks,
         fn Block.T {args, statements, label, ...} =>
            (Vector.foreach (args, fn (v, _) => setVarDef (v, label)) ;
             Vector.foreach (statements,
               fn s => Statement.foreachDef (s,
                  fn (v, _) => setVarDef (v, label)))))

      val {get=labelInfo, set=setLabelInfo, destroy=destLabelInfo} =
         Property.destGetSet (Label.plist,
            Property.initRaise ("DeduplicateBlocks.transform.labelBlock", Label.layout))
      val _ = Vector.foreach (blocks,
         fn b as Block.T {label, ...} =>
            setLabelInfo (label, {block=b, labels=[], vars=[]}))


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
            getI
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
      val varSupply = mkSupply (Var.newString "xx", Var.new)
      val labelSupply = mkSupply (Label.newString "LL", Label.new)


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

               val (swapLabel, labels) = mkSwap {supply=labelSupply, hash=Label.hash, equals=Label.equals}
               val (swapVar, vars) = mkSwap {supply=varSupply, hash=Var.hash, equals=Var.equals}
               val b = Block.replaceLabels (b, swapLabel)
               val b = Block.replaceVars (b,
                  fn (v, t) => (swapVar v, t))
               (* label still refers to the original label, before swapping *)
               val id = Buffer.length labels

               val _ = Buffer.add (labels, label)
               val _ = HashTable.insertIfNew (equivClasses,
                  b, fn () => ref Set.singleton (Label id),
                  fn s => s := Set.add (!s, Label id))
               val {block, ...} = labelInfo label
               val _ = setLabelInfo (label, {block=block, labels=(!labels), vars=(!vars)})
            in
               ()
            end)
      val data = Vector.toList (Buffer.toVector labels)

      val _ = Control.diagnostic (fn () =>
         (Layout.str o Int.toString) (HashTable.size equivClasses))

      val _ = destVarDef ()
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
