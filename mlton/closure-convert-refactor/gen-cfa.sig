signature GEN_CFA_STRUCTS =
sig
   structure Sxml: SXML
   structure Alloc: ALLOCATOR
   sharing Alloc.Sxml = Sxml
end
