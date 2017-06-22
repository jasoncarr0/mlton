(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

structure Scan: SCAN =
struct

fun first ss charRdr strm =
   case ss of
      [] => NONE
    | s::ss =>
         (case s charRdr strm of
             SOME (x, strm') => SOME (x, strm')
           | NONE => first ss charRdr strm)

fun chars cs charRdr strm =
   case cs of
      [] => SOME ((), strm)
    | c::cs => (case charRdr strm of
                   SOME (c', strm') =>
                      if c = c' then chars cs charRdr strm' else NONE
                 | _ => NONE)

fun string s = chars (String.explode s)

fun stringAs (s, x) charRdr strm =
   case string s charRdr strm of
      SOME ((), strm') => SOME (x, strm')
    | NONE => NONE
end
