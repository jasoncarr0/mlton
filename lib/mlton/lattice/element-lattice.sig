(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ELEMENT_LATTICE_STRUCTS =
   sig
      structure Element:
         sig
            type t

            val equals: t * t -> bool
            val hash: t -> Word.t
            val layout: t -> Layout.t
         end
   end

signature ELEMENT_LATTICE =
   sig
      include ELEMENT_LATTICE_STRUCTS

      type t

      val << : Element.t * t -> bool (* force set to contain elt *)
      (* if the lattice doesn't have an element, conditionally add it *)
      (* no guarantee about when the condition is called *)
      val <<? : Element.t * t * (unit -> bool) -> bool 
      val <= : t * t -> bool (* force rhs to be superset of lhs *)
      (* create a new bottom lattice *)
      val empty: unit -> t
      val hasElement: t * Element.t -> bool
      (* does this lattice contain no elements, isBottom empty should be true for non-trivial lattices *)
      val isBottom: t -> bool
      (* does this lattice contain all elements? Need not ever be true *)
      val isTop: t -> bool
      val layout: t -> Layout.t
      val singleton: Element.t -> t
      val fromList: Element.t list -> t
      (* called whenever the values represented by the lattice change, and when called *)
      val whenChanged: t * (unit -> unit) -> unit
   end
