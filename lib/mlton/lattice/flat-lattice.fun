(* Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor FlatLattice (S: FLAT_LATTICE_STRUCTS): FLAT_LATTICE =
struct

open S

structure Elt =
   struct
      datatype t =
         Bottom
       | Point of Element.t
       | Top

      local
         open Layout
      in
         val layout =
            fn Bottom => str "Bottom"
             | Point p => Element.layout p
             | Top => str "Top"
      end
   end
datatype z = datatype Elt.t

datatype t = T of {lessThan: t list ref,
                   upperBound: Element.t option ref,
                   value: Elt.t ref,
                   handlers: (unit -> unit) list ref}

fun layout (T {value, ...}) = Elt.layout (!value)

fun empty () = T {lessThan = ref [],
                  upperBound = ref NONE,
                  value = ref Bottom,
                  handlers = ref []}

val isBottom =
   fn (T {value = ref Bottom, ...}) => true
    | _ => false
val isElement =
   fn (T {value = ref (Point _), ...}) => true
    | _ => false
fun hasElement (T {value, ...}, p) =
   case !value of
       Top => true
     | Point p' => Element.equals (p, p')
     | Bottom => false
val isElementEq = 
   fn (T {value = ref (Point p), ...}, p') => Element.equals (p, p')
    | _ => false
val getElement =
   fn (T {value = ref (Point p), ...}) => SOME p
    | _ => NONE
val isTop =
   fn (T {value = ref Top, ...}) => true
    | _ => false

fun forceTop (T {upperBound, value, handlers, ...}): bool =
   if isSome (!upperBound)
      then false
   else (value := Top; 
         List.foreach (!handlers, fn h => h ());
         true)

fun up (T {lessThan, upperBound, value, handlers, ...}, e: Elt.t): bool =
   let
      fun continue e = List.forall (!lessThan, fn z => up (z, e))
      fun setTop () =
         not (isSome (!upperBound))
         andalso (value := Top;
                  List.foreach (!handlers, fn h => h ());
                  continue Top)
   in
      case (!value, e) of
         (_, Bottom) => true
       | (Top, _) => true
       | (_, Top) => setTop ()
       | (Bottom, Point p) =>
            (value := Point p;
             List.foreach (!handlers, fn h => h ());
             (case !upperBound of
                 NONE => continue (Point p)
               | SOME p' =>
                    Element.equals (p, p') andalso continue (Point p)))
       | (Point p, Point p') => Element.equals (p, p') orelse setTop ()
   end

val op <= : t * t -> bool =
   fn (T {lessThan, value, ...}, e) =>
   (List.push (lessThan, e)
    ; up (e, !value))

val op <= =
   Trace.trace2 ("FlatLattice.<=", layout, layout, Bool.layout)
   (op <=)

fun lowerBound (e, p): bool = up (e, Point p)

val lowerBound =
   Trace.trace2 ("FlatLattice.lowerBound", layout, Element.layout, Bool.layout)
   lowerBound

fun upperBound (T {upperBound = r, value, ...}, p): bool =
   case !r of
      NONE => (r := SOME p
               ; (case !value of
                     Bottom => true
                   | Point p' => Element.equals (p, p')
                   | Top => false))
    | SOME p' => Element.equals (p, p')

val upperBound =
   Trace.trace2 ("FlatLattice.upperBound", layout, Element.layout, Bool.layout)
   upperBound

fun op << (p, e) = lowerBound (e, p)

fun op <<? (p, e as T {upperBound, value, ...}, cond) = case (!value, !upperBound) of
    (Top, _) => true
  | (_, SOME p') => if Element.equals (p, p') orelse not (cond ())
                then true
                else lowerBound (e, p)
  | (Point p', _) => if Element.equals (p, p') andalso not (cond ())
                then true 
                else lowerBound (e, p)
  | _ => if cond () then lowerBound (e, p) else true

fun forceElement (e, p) =
   lowerBound (e, p) andalso upperBound (e, p)

val forceElement =
   Trace.trace2 ("FlatLattice.forceElement", layout, Element.layout, Bool.layout)
   forceElement

fun singleton p =
   let
      val e = empty ()
      val _ = forceElement (e, p)
   in
      e
   end

val singleton = Trace.trace ("FlatLattice.point", Element.layout, layout) singleton

fun fromList ps = case List.removeDuplicates (ps, Element.equals) of
   [] => empty ()
 | [p] => singleton p
 | _ => let 
           val e = empty ()
           val _ = forceTop e
        in
           e
        end

fun whenChanged (T {handlers, ...}, h) =
   (List.push (handlers, h);
    h ())

end
