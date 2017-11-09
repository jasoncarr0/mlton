(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor PowerSetLattice_ListSet (S: POWERSET_LATTICE_STRUCTS): POWERSET_LATTICE =
struct

open S

structure Elt = Element

structure EltSet :>
   sig
      type t
      val add: t * Elt.t -> t
      val contains: t * Elt.t -> bool
      val empty: t
      val foreach: t * (Elt.t -> unit) -> unit
      val fromList: Elt.t list -> t
      val keepAll: t * (Elt.t -> bool) -> t
      val isEmpty: t -> bool
      val layout: t -> Layout.t
      val singleton: Elt.t -> t
      val size: t -> int
      val toList: t -> Elt.t list
   end =
   struct
      type t = Elt.t list
      val {add, contains, empty, singleton, size, ...} =
         List.set {equals = Elt.equals, layout = Elt.layout}
      val foreach = List.foreach
      fun fromList es = List.removeDuplicates (es, Elt.equals)
      val keepAll = List.keepAll
      val isEmpty = List.isEmpty
      fun layout es =
         Layout.seq [Layout.str "{",
                     (Layout.fill o Layout.separateRight)
                     (List.map (es, Elt.layout), ","),
                     Layout.str "}"]
      val toList = fn es => es
   end

datatype t = T of {elements: EltSet.t ref,
                   handlers: (Elt.t -> unit) list ref,
                   filter: (Elt.t -> bool) ref,
                   topSize: int option ref}

fun layout (T {elements, ...}) =
   EltSet.layout (!elements)

fun new es = T {elements = ref es,
                handlers = ref [],
                filter = ref (fn x => true),
                topSize = ref NONE}

fun empty () = new EltSet.empty
fun singleton e = new (EltSet.singleton e)
fun fromList es = new (EltSet.fromList es)

fun getElements (T {elements, ...}) =
   EltSet.toList (!elements)
fun hasElement (T {elements, ...}, e) =
   EltSet.contains(!elements, e)

fun addHandler (T {elements, handlers, ...}, h) =
   (List.push (handlers, h);
    EltSet.foreach (!elements, fn e => h e))

fun whenChanged (T {elements, handlers, ...}, h) =
   (List.push (handlers, fn _ => h ());
    h ())


fun op<<? (e, T {elements, handlers, filter, topSize, ...}, cond) =
   if EltSet.contains (!elements, e) orelse not (cond ())
      then true
      else if !filter e 
         then (elements := EltSet.add (!elements, e);
               List.foreach (!handlers, fn h => h e);
               true)
         else false
fun op<< (e, es) = <<? (e, es, fn () => true)

fun isTop (T {elements, topSize, ...}) = Option.exists (!topSize, fn i => EltSet.size (!elements) >= i)
fun isBottom (T {elements, ...}) = case EltSet.toList (!elements) of
    [] => true
  | _ => false

fun op<= (es as T {elements, topSize, ...}, es') =
   if isTop es
   then false
   else (addHandler(es, fn e => ignore (<< (e, es'))); true)


fun setTop (T {elements, filter, topSize, ...}, bound) =
   case !topSize of
       NONE => (filter := (fn x => List.contains (bound, x, Elt.equals));
                elements := EltSet.keepAll(!elements, !filter);
                topSize := SOME (List.length bound);
                true)
     | _ => false


end


functor PowerSetLattice_UniqueSet (S: POWERSET_LATTICE_STRUCTS): POWERSET_LATTICE =
struct

open S

structure Elt = Element

structure EltSet = UniqueSet (structure Element = Element
                              val cacheSize: int = 7
                              val bits: int = 13)
structure EltSet =
   struct
      open EltSet
      fun layout es =
         Layout.seq [Layout.str "{",
                     (Layout.fill o Layout.separateRight)
                     (List.map (toList es, Elt.layout), ","),
                     Layout.str "}"]
   end


datatype t = T of {elements: EltSet.t ref,
                   handlers: (Elt.t -> unit) list ref,
                   coercedTo: t list ref,
                   top: EltSet.t option ref}

fun equals (T {elements = elements1, ...}, T {elements = elements2, ...}) =
   elements1 = elements2

fun layout (T {elements, ...}) =
   EltSet.layout (!elements)

fun new es = T {elements = ref es,
                handlers = ref [],
                coercedTo = ref [],
                top = ref NONE}

fun empty () = new EltSet.empty
fun singleton e = new (EltSet.singleton e)
fun fromList es = new (EltSet.fromList es)

fun getElements (T {elements, ...}) =
   EltSet.toList (!elements)
fun hasElement (T {elements, ...}, e) =
   EltSet.isEmpty (EltSet.- (EltSet.singleton e, !elements))

fun addHandler (T {elements, handlers, ...}, h) =
   (List.push (handlers, h);
    EltSet.foreach (!elements, fn e => h e))

fun whenChanged (T {handlers, ...}, h) =
   (List.push (handlers, fn _ => h ());
    h ())

fun send (T {elements, handlers, coercedTo, top, ...}, es, cond) =
   let
      val es = Option.fold (!top, es, fn (e, t) => EltSet.intersect (e, t))
      val diff = EltSet.- (es, !elements)
   in
      if EltSet.isEmpty diff orelse not (cond ())
         then ()
         else (elements := EltSet.+ (diff, !elements);
               List.foreach (!coercedTo, fn to => send (to, diff, fn () => true));
               List.foreach (!handlers, fn h =>
                             EltSet.foreach (diff, fn e => h e)))
   end

fun op<= (from as T {elements, coercedTo, ...}, to) =
   if List.exists (!coercedTo, fn es => equals (es, to))
      then true
      else (List.push (coercedTo, to); 
            send (to, !elements, fn () => true);
            true)

fun op<<? (e, es, cond) =
   (send (es, EltSet.singleton e, cond);
    true)
fun op<< (e, es) = <<? (e, es, fn () => true)

fun isTop (T {elements, top, ...}) = Option.exists (!top, fn t => EltSet.equals(!elements, t))
fun isBottom (T {elements, ...}) = EltSet.isEmpty (!elements)

fun setTop (T {elements, top, ...}, bound) =
   case !top of
       NONE => (top := SOME (EltSet.fromList bound);
                elements := EltSet.intersect (!elements, Option.valOf (!top));
                true)
     | _ => false

end
