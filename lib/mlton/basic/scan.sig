(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature SCAN =
   sig
      val first: ((char,'a) StringCvt.reader -> ('b,'a) StringCvt.reader) list ->
                 (char,'a) StringCvt.reader -> ('b,'a) StringCvt.reader
      val string: string -> (char,'a) StringCvt.reader -> (unit,'a) StringCvt.reader
      val stringAs: (string * 'b) -> (char,'a) StringCvt.reader -> ('b,'a) StringCvt.reader
   end
