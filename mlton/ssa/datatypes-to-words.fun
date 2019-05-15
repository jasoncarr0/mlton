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

fun transform (Program.T {datatypes, main, functions, ...}) =
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



      (* for successor, we'll need to check overflow, so it can't be an expression,
       * at this level *)
      fun handleExp (oom, one) exp =
         case exp of

      datatype Line =
           Statement of Statement.t
         | Transfer of (Label.t -> Transfer.t)
      fun handleStatement (oom, one, buf) st =
         case st of
              Statement.Bind {exp, ty, var} =>
              let
                 val (exp, check) =
                  case exp of
                       Exp.Inject {sum, variant} =>
                          case tyconRepr sum of
                               Finite => (Exp.Var variant, NONE)
                             | Nat => (Exp.Var variant, NONE)
                             | _ => (exp, NONE)
                     | Exp.Object {con, args} =>
                          case conVal con of
                               Word i => (* TODO: make WordX instead of word, can be different sizes *)
                                 ((Exp.Const o Const.word o WordX.fromIntInf)
                                 (Integer.toIntInf (Word.toInt i), WordSize.word32),
                                  NONE)
                              (*
                             | Successor =>
                                  if 1 = Vector.length args
                                    then let
                                       val v = (Vector.new2 one (Vector.sub (args, 0)))
                                    in
                                       (Exp.PrimApp
                                       {args=v,
                                        prim=Prim.Word_add WordSize.word64},
                                        SOME v)
                                    end
                                    else MLton.bug "DatatypesToWords.transform: Incorrect arguments for successor constructor"
                               *)

                  val _ =
                     Buffer.push (buf, Statement (Statement.Bind {exp=handleExp exp, ty=handleTy ty, var=var}))
                  val _ =
                     case check of
                          SOME v' =>
                             let
                                val checkVar = Var.newString "succCheck"
                              in
                              (Buffer.push (buf, Statement
                                 (Statement.Bind
                                    {exp={args=v, prim=Prim.Word_addCheckP WordSize.word64},
                                     ty=Type.word32,
                                     var=checkVar})));
                              (Buffer.push (buf, Transfer (fn l =>
                                 Transfer.Case {cases = Cases.Word
                                    (WordSize.word32, Vector.new1 (WordX.zero WordSize.64, oom)),
                                     default = SOME l,
                                     test = checkVar})))
                             end
                        | NONE =>
                             ()
              in
                 ()
              end
            | _ => Buffer.push (buf, Statement st)

      fun handleBlock (Block.T {args, label, statements, transfer}) =
         let
            val args = Vector.map (args, fn (v, ty) => (v, handleType ty))
            val buffer = Buffer.new {dummy=Transfer Transfer.Bug}
            val _ = Vector.foreach (statements,
               handleStatement)
         in
            createBlocks buffer
         end

      fun handleFun {args, blocks, mayInline, name, raises, returns, start} =
         let
            val blocks = Buffer.new {dummy=
               Block.T {args=Vector.new0 (), label=Label.bogus (),
                        statements=Vector.new0 (), transfer=Transfer.Bug}}
            val _ = 
            val blocks = Buffer.toVector blocks
         {args=args, blocks=blocks, mayInline=mayInline, name=name,
          raises=raises, returns=returns, start=start}

   in
   end



