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
      val layout: t -> Layout.t
      val singleton: Elt.t -> t
      val toList: t -> Elt.t list
   end =
   struct
      type t = Elt.t list
      val {add, contains, empty, singleton, ...} =
         List.set {equals = Elt.equals, layout = Elt.layout}
      val foreach = List.foreach
      fun fromList es = List.removeDuplicates (es, Elt.equals)
      fun layout es =
         Layout.seq [Layout.str "{",
                     (Layout.fill o Layout.separateRight)
                     (List.map (es, Elt.layout), ","),
                     Layout.str "}"]
      val toList = fn es => es
   end


datatype source = Copying of (source ref * (unit -> EltSet.t))
                | Initialized of EltSet.t
                | Uninitialized
datatype t = T of {eltSource: source ref,
                   handlers: (Elt.t -> unit) list ref}
fun hom (f: EltSet.t -> 'a, uninit: unit -> 'a, eltSource: source ref): 'a = 
   let
      fun loop src = case src of
         Copying (_, els) => f (els ())
       | Initialized els => f els
       | Uninitialized => uninit ()
   in
      loop (!eltSource)
   end

fun layout (T {eltSource, ...}) =
   hom (EltSet.layout, fn () => Layout.str "{}", eltSource)

fun new es = T {eltSource = ref es,
                handlers = ref []}

fun empty () = new Uninitialized
fun singleton e = new (Initialized (EltSet.singleton e))
fun fromList es = new (Initialized (EltSet.fromList es))

fun getElements (T {eltSource, ...}) =
   hom (EltSet.toList, fn () => [], eltSource)

fun addHandler (T {eltSource, handlers, ...}, h) =
   (List.push (handlers, h);
    hom (fn s => EltSet.foreach (s, fn e => h e), fn () => (), eltSource))

(* always inintializes *)
fun addAndInit (els, e, T {eltSource, handlers, ...}) =
   (eltSource := Initialized (EltSet.add (els, e));
    List.foreach (!handlers, fn h => h e))
fun op<< (e, es as T {eltSource, handlers, ...}) =
   case !eltSource of
       Copying (src, srcEls) =>
         if EltSet.contains (srcEls (), e)
         then ()
         else addAndInit (srcEls (), e, es)
     | Initialized els =>
          if EltSet.contains (els, e)
          then ()
          else addAndInit (els, e, es)
     | Uninitialized => 
          (eltSource := Initialized (EltSet.singleton e);
           List.foreach (!handlers, fn h => h e))

(* the mechanics of this rely on only being called for the actual source *)
fun flowFromCopySource (e, es as T {eltSource, handlers, ...}) =
   case (!eltSource) of
       (Copying _) => List.foreach (!handlers, fn h => h e)
     | (Initialized els) => op<< (e, es)
       (* can't happen *)
     | _ => Error.bug "PowerSetLattice_ListSet.flowFromCopySource"

fun op<= (es as T {eltSource, ...}, es' as T {eltSource=eltSource', ...}) =
   case (!eltSource, !eltSource') of
      (Copying (src, srcEls), Uninitialized) =>
      let
          fun loop s = if s = eltSource'
             then true
             else case !s of
                  Copying (s', _) => loop s'
                | _ => false
          val cycles = loop src
      in
         if cycles
         then (eltSource' := Initialized (srcEls ()); addHandler (es, fn e => << (e, es')))
         else (eltSource' := Copying (eltSource, srcEls); addHandler (es, fn e => flowFromCopySource (e, es')))
      end
    | (Initialized els, Uninitialized) =>
       let
          fun getEls es = case es of
              Initialized els => els
            | Uninitialized => EltSet.empty
            | Copying (_, els) => els ()
          val _ = eltSource' := Copying (eltSource, fn () => getEls (!eltSource))
          val _ = addHandler (es, fn e => flowFromCopySource (e, es'))
       in
          ()
       end
    | _ => addHandler(es, fn e => << (e, es'))

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
                   coercedTo: t list ref}

fun equals (T {elements = elements1, ...}, T {elements = elements2, ...}) =
   elements1 = elements2

fun layout (T {elements, ...}) =
   EltSet.layout (!elements)

fun new es = T {elements = ref es,
                handlers = ref [],
                coercedTo = ref []}

fun empty () = new EltSet.empty
fun singleton e = new (EltSet.singleton e)
fun fromList es = new (EltSet.fromList es)

fun getElements (es as T {elements, ...}) =
   EltSet.toList (!elements)

fun addHandler (T {elements, handlers, ...}, h) =
   (List.push (handlers, h);
    EltSet.foreach (!elements, fn e => h e))

fun send (T {elements, handlers, coercedTo}, es) =
   let
      val diff = EltSet.- (es, !elements)
   in
      if EltSet.isEmpty diff
         then ()
         else (elements := EltSet.+ (diff, !elements);
               List.foreach (!coercedTo, fn to => send (to, diff));
               List.foreach (!handlers, fn h =>
                             EltSet.foreach (diff, fn e => h e)))
   end

fun op<= (from as T {elements, coercedTo, ...}, to) =
   if List.exists (!coercedTo, fn es => equals (es, to))
      then ()
      else (List.push (coercedTo, to)
            ; send (to, !elements))

fun op<< (e, es) =
   send (es, EltSet.singleton e)

end
