(* Copyright (C) 2019 Jason Carr           
 *    
 * MLton is released under a HPND-style license.    
 * See the file MLton-LICENSE for details.    
 *)

(* Hopcroft's DFA Minimization algorithm,
 * Used here primarily for deduplication *)
signature HOPCROFT_STRUCTS = sig
   structure Set: SET
   structure Alphabet: sig
      type t
      val equals: t * t -> bool
   end
end
signature HOPCROFT = sig
   open HOPCROFT_STRUCTS
   type u = Set.Element.t
   type s = Alphabet.t

   val run: {
      initialPartition: u list list,
      transitionsFrom: u -> s list,
      transition: u * u * s -> bool
   }
   -> u list list
end

