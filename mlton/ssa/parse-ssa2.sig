(* Copyright (C) 2018 Manan Joshi.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

 signature PARSE_SSA2_STRUCTS =
    sig
       structure SsaTree2: SSA_TREE2
    end
 signature PARSE_SSA2 =
    sig
       include PARSE_SSA2_STRUCTS

       val program: SsaTree2.Program.t Parse.t
    end
