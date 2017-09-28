signature LATTICE_STRUCTS =
   sig
   end

signature LATTICE =
   sig
      include LATTICE_STRUCTS

      type t

      val <=: t * t -> unit (* force rhs to be upped to lhs *)
      val new: unit -> t
      val whenUpdate: (t -> unit) -> unit
   end
