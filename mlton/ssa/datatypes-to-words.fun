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
 | Word of WordX.t
 | Successor of WordSize.t

fun transform2 (Program.T {datatypes, functions, globals, main}) =
   let
      val {get=tyconRepr, set=setTyconRepr, ...} =
         Property.getSetOnce (Tycon.plist, Property.initConst Unchanged)

      val {get=conVal, set=setConVal, ...} =
         Property.getSet (Con.plist, Property.initConst Constructor)


      val natSize = WordSize.objptr ()
      val natType = Type.word natSize
      (* One consideration here might be bool,
       * but we'd have to be a bit more careful about size.
       * Bool is made into a word32 on many platforms for C compatibility *)
      val finiteSize = WordSize.word32
      val finiteType = Type.word finiteSize
      val datatypes = Vector.keepAll (datatypes, fn Datatype.T {cons, tycon} =>
         if Vector.forall (cons, fn {args, ...} => Prod.isEmpty args)
            then (setTyconRepr (tycon, Finite);
               (* Later: set based on frequent occurence
                * to make good use of zero/nonzero *)
                  (Vector.foreachi (cons, fn (i, {con, ...}) =>
                  setConVal (con, (Word o WordX.fromIntInf)
                     (Int.toIntInf i, WordSize.word32))));
                  false)
         else if Vector.length cons = 2
            andalso Vector.exists (cons, fn {args, ...} => Prod.isEmpty args)
            andalso Vector.exists (cons, fn {args, ...} =>
               Prod.length args = 1
                  andalso
                     case Prod.sub (args, 0) of
                        {elt, isMutable=true} =>
                           Type.equals (elt, Type.datatypee tycon)
                      | _ => false)
            then
               (setTyconRepr (tycon, Nat);
                Vector.foreach (cons, fn {con, args} =>
                  setConVal (con, if Prod.isEmpty args
                     then Word (WordX.zero natSize)
                     else Successor natSize)); false)
         else true)

      val (globals, one) =
         case Vector.peekMap (globals,
            fn Statement.Bind {exp=Exp.Const (Const.Word wx), var=SOME var, ...} =>
               if WordSize.equals (WordX.size wx, natSize)
                  andalso WordX.isOne wx
               then SOME var
               else NONE
             | _ => NONE) of
            (SOME v) => (globals, v)
            (* Should absolutely not happen but just in case *)
          | NONE =>
            let
               val v = Var.newNoname ()
               val ty = Type.word natSize
               val exp = Exp.Const (Const.Word (WordX.one natSize))
               val st = Statement.Bind {var=SOME v, ty=ty, exp=exp}
            in
               (Vector.concat [globals, Vector.new1 st], v)
            end

      fun handleType (ty: Type.t): Type.t =
         case Type.dest ty of
              Type.Datatype tycon =>
                  (case tyconRepr tycon of
                        Nat => natType
                      | Finite => finiteType
                      | Unchanged => ty)
            | _ => ty

      (* some changes require interrupting simple control flow,
       * so we'll need to handle intermediate transfers *)
      datatype Instruction =
           Statement of Statement.t
         | Transfer of (Label.t -> Transfer.t)

      fun handleTransfer blocks t =
         case t of
              Transfer.Case {cases=Cases.Con cases, default, test} =>
                 if not (Vector.isEmpty cases)
                     (* Assume still well-typed *)
                  then
                     case conVal (#1 (Vector.first cases)) of
                         Word wx =>
                           let
                              val size = WordX.size wx
                              val successor = ref NONE
                              val cases = Cases.Word (size,
                                 Vector.keepAllMap (cases,
                                 fn (c, l) =>
                                    case conVal c of
                                         Word i => SOME (i, l)
                                       | Successor _ => (successor := SOME l; NONE)
                                       | _ => Error.bug "DatatypesToWords.transform: Inconsistent cases"))
                              (* for successor, also need to decrement by one *)
                              val default =
                                 case !successor of
                                    SOME l =>
                                       let
                                          val decVar = Var.new test
                                          val decLabel = Label.newNoname ()
                                          val decBlock = Block.T
                                             {args=Vector.new0 (),
                                              label=decLabel,
                                              statements=Vector.new1
                                                (Statement.Bind
                                                   {exp=Exp.PrimApp
                                                      {args=Vector.new2 (test, one),
                                                       prim=Prim.wordSub size},
                                                    ty=Type.word size,
                                                    var=SOME decVar}),
                                              transfer=Transfer.Goto
                                                {args=Vector.new1 decVar,
                                                 dst=l}}
                                          val _ = Buffer.add (blocks, decBlock)
                                       in
                                          SOME decLabel
                                       end
                                  | NONE => default
                           in
                              Transfer.Case {cases=cases, default=default, test=test}
                           end
                       | _ => t
                  else t
            | _ => t




      fun handleStatement (oom, instrs) st =
         case st of
              Statement.Bind {exp, ty, var} =>
              let
                 val (exp, check) =
                  case exp of
                       Exp.Inject {sum, variant} =>
                          (case tyconRepr sum of
                               Finite => (Exp.Var variant, NONE)
                             | Nat => (Exp.Var variant, NONE)
                             | _ => (exp, NONE))
                     | Exp.Object {con=SOME con, args} =>
                          case conVal con of
                               Word i =>
                                 (Exp.Const (Const.word i), NONE)
                             | Successor sz =>
                                  if 1 = Vector.length args
                                    then let
                                       val v = (Vector.new2 (one, (Vector.sub (args, 0))))
                                    in
                                       (Exp.PrimApp
                                       {args=v,
                                        prim=Prim.wordAdd sz},
                                        SOME v)
                                    end
                                    else Error.bug
                                    "DatatypesToWords.transform: Incorrect arguments for successor constructor"
                     | _ => (exp, NONE)
                  val _ =
                     List.push (instrs, Statement (Statement.Bind {exp=exp, ty=handleType ty, var=var}))
                  val _ =
                     case check of
                          SOME v' =>
                             let
                                val checkVar = Var.newString "succCheck"
                              in
                              (List.push (instrs, Statement
                                 (Statement.Bind
                                    {exp=Exp.PrimApp
                                       {args=v', prim=Prim.wordAddCheckP (WordSize.word64, {signed=false})},
                                     ty=natType,
                                     var=SOME checkVar})));
                              (List.push (instrs, Transfer (fn l =>
                                 Transfer.Case {cases=Cases.Word
                                    (natSize, Vector.new1 (WordX.zero natSize, oom)),
                                     default=SOME l,
                                     test=checkVar})))
                             end
                        | NONE =>
                             ()
              in
                 ()
              end
            | _ => List.push (instrs, Statement st)

      (* given a sequence of statements and transfers,
       * create new blocks as necessary;
       * assuming the last transfer does not need a destination
       * block and conlcudes the sequence
       * args only affects the first block created *)
      fun createBlocks blocks (instrs, acc, args, label) =
         case instrs of
              Statement st :: instrs =>
                  createBlocks blocks (instrs, st :: acc, args, label)
            | Transfer ft :: instrs =>
                  let
                     val l' = Label.new label
                     val t = ft l'
                     val block = Block.T
                        {args=args,
                         label=label,
                         statements=Vector.fromList acc,
                         transfer=t}
                     val _ = Buffer.add (blocks, block)
                  in
                     createBlocks blocks (instrs, [], Vector.new0 (), label)
                  end
            | [] => ()

      fun handleBlock (oom, blocks) (Block.T {args, label, statements, transfer}) =
         let
            val args = Vector.map (args, fn (v, ty) => (v, handleType ty))
            val instrs = ref []
            val _ = Vector.foreach (statements, handleStatement (oom, instrs))
            val _ = List.push (instrs, Transfer (fn _ => handleTransfer blocks transfer))
         in
            createBlocks blocks (List.rev (!instrs), [], args, label)
         end

      fun handleFun {args, blocks, mayInline, name, raises, returns, start} =
         let
            val buf = Buffer.new {dummy=
               Block.T {args=Vector.new0 (), label=Label.bogus,
                        statements=Vector.new0 (), transfer=Transfer.Bug}}
            val oom = Label.newString "Nat_OutOfMemory"
            val _ = Vector.foreach (blocks, handleBlock (oom, buf))

            val oomBlock = Block.T {args=Vector.new0 (), label=oom,
                                    statements=Vector.new0 (),
                                    (* TODO *)
                                    transfer=Transfer.Bug}
            val _ = Buffer.add (buf, oomBlock)
            val blocks = Buffer.toVector buf
         in
            Function.new
            {args=args, blocks=blocks, mayInline=mayInline, name=name,
             raises=raises, returns=returns, start=start}
         end

   in
      Program.T {datatypes=datatypes, globals=globals, functions=functions, main=main}
   end


end
