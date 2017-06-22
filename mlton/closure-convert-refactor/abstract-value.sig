(* Copyright (C) 2009,2016 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ABSTRACT_VALUE_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature ABSTRACT_VALUE =
   sig
      include ABSTRACT_VALUE_STRUCTS

      type t

      datatype dest =
         Array of t
       | Lambdas of Sxml.Lambda.t list
       | Ref of t
       | Tuple of t vector
       | Type of Sxml.Type.t (* type doesn't contain any arrows *)
       | Vector of t
       | Weak of t

      val addHandler: t * (Sxml.Lambda.t -> unit) -> unit
      val coerce: {from: t, to: t} -> unit
      val dest: t -> dest
      (* Destroy info associated with Sxml.Type used to keep track of arrows. *)
      val destroy: unit -> unit
      val fromType: Sxml.Type.t -> t
      val lambda: Sxml.Lambda.t -> t
      val layout: t -> Layout.t
      (* In tuple vs, there must be one argument that is not Type _. *)
      val tuple: t vector -> t
      val typeIsFirstOrder: Sxml.Type.t -> bool
      val unify: t * t -> unit
   end
