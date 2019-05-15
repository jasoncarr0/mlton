(* This pass changes the representation of enumeration datatypes
 * and natlike datatypes to be words with arithmetic,
 * to improve binary for the former, and
 * speed/memory for the latter.
 *
 * Waiting until late in the pipeline helps us catch the most
 * types but also misses some opportunity for e.g. loop optimizations
 *)

functor DatatypesToWords (S: SSA2_TRANSFORM_STRUCTS): SSA2_TRANSFORM = 
struct

open S

datatype Repr =
   Unchanged
 | Finite
 | Nat

datatype ConVal =
   Constructor
 | Unset
 | Word of word
 | Successor

fun makeTransform (Program.T {datatypes, main, functions, ...}) =
   let
      val {get=tyconRepr, set=setTyconRepr} =
         Property.getSetOnce (Tycon.plist, Property.initConst Unchanged)

      val {get=conVal, set=setConVal} =
         Property.getSet (Con.plist, Property.initConst Constructor)

      val _ = Vector.foreach (datatypes, fn Datatype.T {cons, tycon} =>
         if Vector.forall (cons, fn {args, ...} => Prod.isEmpty args)
            andalso Vector.length cons < 2^32
            then (setTyconRepr (tycon, Finite);
               (* Later: set based on frequent occurence
                * to make good use of zero/nonzero *)
                  Vector.foreachi (cons, fn ({con, ...}, i) => setConVal (con, Word i)))
         else if Vector.length cons = 2
            andalso Vector.exists (cons, fn {args, ...} => Prod.isEmpty args)
            andalso Vector.exists (cons, fn {args, ...} =>
               Prod.length args = 1
                  andalso
                     case Prod.sub (args, 0) of
                        {elt, isMutable=true} =>
                           Type.equals (elt, Type.Datatype tycon)
                      | _ => false)
            then
               (setTyconRepr (tycon, Nat);
                Vector.foreach (cons, fn {con, args} =>
                  setConVal (con, if Prod.isEmpty args then Word 0 else Successor)))

         else ())

      (* TODO: also need to fix globals *)
   in
      fn {args, blocks, mayInline, name, raises, returns, start} =>
         {args=args, blocks=blocks, mayInline=mayInline, name=name,
          raises=raises, returns=returns, start=start}
   end

fun transform (Program.T {datatypes, functions, globals, main}) =



