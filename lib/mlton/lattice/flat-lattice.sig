(* Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature FLAT_LATTICE_STRUCTS =
   sig
      include ELEMENT_LATTICE_STRUCTS
   end

signature FLAT_LATTICE =
   sig
      include ELEMENT_LATTICE

      val forceElement: t * Element.t -> bool
      val forceTop: t -> bool
      val getElement: t -> Element.t option
      val isElement: t -> bool
      val isElementEq: t * Element.t -> bool
      val lowerBound: t * Element.t -> bool
      val upperBound: t * Element.t -> bool
   end
