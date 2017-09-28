(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature POWERSET_LATTICE_STRUCTS =
   sig
      include ELEMENT_LATTICE_STRUCTS
   end
signature POWERSET_LATTICE =
   sig
      include ELEMENT_LATTICE

      val addHandler: t * (Element.t -> unit) -> unit
      val getElements: t -> Element.t list
   end
