(* Copyright (C) 2019 Jason Carr           
 *    
 * MLton is released under a HPND-style license.    
 * See the file MLton-LICENSE for details.    
 *)

(* Hopcroft's DFA Minimization algorithm,
 * Used here primarily for deduplication.
 *
 * For simplicity, we use a set datastructure
 * rather than a proper mutable partition refinement. *)
signature HOPCROFT_STRUCTS = sig
   structure Set: SET
end
signature HOPCROFT = sig
   include HOPCROFT_STRUCTS

   type u = Set.Element.t
   type t

   val run: {
      (* must have at least two components for any work to be
       * performed. One component will return immediately *)
      initialPartition: Set.t list,
      (* Produce a list of state sets which transition to this
       * set of states on the same character.
       * Empty sets are cheap to deal with, so this can just
       * be a proxy for the list of characters *)
      transitionsTo: Set.t -> Set.t list,
      info: (unit -> t) -> u -> {set: t -> unit,
                                 get: unit -> t}
   }
   -> Set.t list
end

functor Hopcroft (S: HOPCROFT_STRUCTS) : HOPCROFT =
struct

open S
structure RA = ResizableArray
   
type u = Set.Element.t
type t = int (* index of set *)

fun run {initialPartition, transitionsTo,
         info: (unit -> t) -> u -> {set: t -> unit,
                                    get: unit -> t}} =
   let
      val infoFor = info (fn () => 0)
      fun getInfo v = #get (infoFor v) ()
      fun setInfo (v, i) = #set (infoFor v) i

      val worklist = RA.empty ()
      val sets = RA.empty ()

      val _ =
         case initialPartition of
              x :: xs =>
                  (RA.addToEnd (sets, x) ;
                   List.foreachi (xs,
                     fn (i, s) =>
                        (RA.addToEnd (sets, s) ;
                         Set.foreach (s,
                           fn e => setInfo (e, i + 1)) ;
                         RA.addToEnd (worklist, (i + 1, s)))))
            | _ => raise Fail "Hopcroft.run: initial partition must contain at least one set"

      fun splitBy x =
         let
            (* this is also O(n^2) rather than O(nlogn) but it shouldn't matter too much *)
            val splits = List.removeDuplicates (List.map (Set.toList x, getInfo), op =)
            val _ = List.foreach (splits,
               fn i =>
                  let
                     val s = RA.sub (sets, i)
                     val sx = Set.intersect (s, x)
                     val snx = Set.subset (s, fn e => not (Set.contains (x, e)))

                     val inx = RA.length sets
                     val _ =
                        if Set.isEmpty sx orelse Set.isEmpty snx
                        then ()
                        else
                           (RA.addToEnd (sets, snx) ;
                           RA.update (sets, i, sx) ;
                           Set.foreach (snx,
                              fn y => setInfo (y, inx)) ;
                           case RA.index (worklist, fn (j, _) => i = j) of
                                SOME k =>
                                   (RA.update (worklist, k, (i, sx)) ;
                                    RA.addToEnd (worklist, (inx, snx)))
                              | NONE =>
                                 if Set.size sx < Set.size snx
                                    then RA.addToEnd (worklist, (i, sx))
                                 else RA.addToEnd (worklist, (inx, snx)))
                  in
                     ()
                  end)
         in
            ()
         end

      fun process (_, w) =
         let
            val _ = Control.diagnostic
               (fn () =>
               let open Layout in
                  seq [str "Hopcroft: Processing set ", Set.layout w, str " out of ",
                       Int.layout (RA.length worklist), str " remaining"]
               end)
         in
            List.foreach (transitionsTo w, splitBy)
         end

      val _ =
         while 0 < RA.length worklist do
            (process (RA.deleteLast worklist))
   in
      RA.toList sets
   end

end
