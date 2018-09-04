(* Copyright (C) 2018 Manan Joshi.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

 functor ParseSsa2(S: PARSE_SSA2_STRUCTS) : PARSE_SSA2  =
 struct
 open S
 open SsaTree2
 structure P = Parse
 open P.Ops
 infix 1 <|> >>=
 infix  3 <*> <* *>
 infixr 4 <$> <$$> <$$$> <$$$$> <$ <$?>

 fun isInfixChar b = case List.index
    (String.explode "!%&$#+-/:<=>?@\\~'^|*",
     fn c => b = c) of
        SOME _ => true
      | NONE   => false

 fun isIdentFirst b = Char.isAlpha b orelse b = #"'"
 fun isIdentRest b = Char.isAlphaNum b orelse b = #"'" orelse b = #"_" orelse b = #"."

 val stringToken = (fn (x, y) => [x, y]) <$$> (P.char #"\\", P.next) <|>
                   (fn x      => [x]   ) <$> P.next

 fun skipComments () = P.any
     [P.str "(*" *> P.cut (P.manyCharsFailing(P.str "*)" <|> P.str "(*") *>
     ((P.str "*)" <|> "" <$ P.delay skipComments) *> P.each [P.next]
     <|> P.failCut "Closing comment")),
     List.concat <$> P.each
     [P.each [P.char #"\""],
     List.concat <$> P.manyFailing(stringToken, P.char #"\""),
     P.each [P.char #"\""]],
     P.each [P.next]]

 fun token s = P.notFollowedBy
    (P.str s,
    (P.char #"_") <|> (P.nextSat Char.isAlphaNum)) <* P.spaces

 fun symbol s = P.notFollowedBy
    (P.str s,
    (P.nextSat (fn b => isInfixChar b orelse b = #"_"))) <* P.spaces

 fun 'a makeNameResolver(f: string -> 'a): string -> 'a =
      let
          val hash = String.hash
          val map = HashSet.new{hash= hash o #1}
          fun eq x (a: string * 'a) = String.equals(x, #1 a)
        in
           fn x => (#2 o HashSet.lookupOrInsert)(map, hash x, eq x, fn () => (x, f x))
        end

 val ident = (String.implode <$> (P.any[(op ::) <$$>
              (P.nextSat isIdentFirst,
               P.many (P.nextSat isIdentRest)),
               List.append <$$>
              (P.many1 (P.nextSat isInfixChar),
              (op ::) <$$> (P.char #"_", P.many (P.nextSat Char.isDigit)) <|> P.pure []
              (* just for collecting _0 *)
              )])) <|> P.failCut "identifier"

 fun parenOf p = (P.char #"(" *> P.spaces *> p <* P.spaces <* P.char #")")

 fun doneRecord' () = P.char #"{" <* P.many(P.delay doneRecord' <|> P.failing(P.char #"}") *> P.next) <* P.char #"}"
 val doneRecord = doneRecord' ()

 fun fromRecord name p = P.peek
                        (P.char #"{" *> P.many (() <$ P.delay doneRecord' <|> () <$ P.failing (token name <* symbol "=") <* P.next)
                        *> token name *> symbol "=" *> p)

 fun casesOf(con, left, right) = Vector.fromList <$> P.sepBy1
                                (left <* P.spaces <* token "=>" >>= (fn l =>
                                 right >>= (fn r => con (l, r))),
                                 P.spaces *> P.char #"|" *> P.spaces)

 fun optionOf p = SOME <$> (token "Some" *> P.cut(p)) <|> NONE <$ token "None"

 fun makeObjectCon resolveCon (ident) = case ident of
                     "tuple"    => ObjectCon.Tuple
                   | "sequence" => ObjectCon.Sequence
                   | _          => ObjectCon.Con (resolveCon ident)

 fun makeProd (elt, isMutable) = {elt = elt, isMutable = isMutable}

 fun makeType resolveTycon resolveCon (args, ident) =
     case ident of
                "cpointer" => Type.cpointer
              | "intInf"   => Type.intInf
              | "real32"   => Type.real RealSize.R32
              | "real64"   => Type.real RealSize.R64
              | "thread"   => Type.thread
              | "weak"     => Type.weak (#elt (Vector.first (Prod.dest (valOf args))))
              | "word8"    => Type.word WordSize.word8
              | "word16"   => Type.word WordSize.word16
              | "word32"   => Type.word WordSize.word32
              | "word64"   => Type.word WordSize.word64
              | "unit"     => Type.unit
              | _          => (case args of
                                  NONE      => Type.datatypee (resolveTycon ident)
                                | SOME args => Type.object {args = args,
                                                            con = makeObjectCon resolveCon ident})

    local

    fun makeType' resolveTycon resolveCon () = (makeType resolveTycon resolveCon) <$$>
                                               (((SOME <$> P.delay (makeProd' resolveTycon resolveCon)) <|> P.pure NONE),
                                               (P.spaces *> ident <* P.spaces))

    and makeProd' resolveTycon resolveCon () = parenOf(Prod.make <$>
                                                      (Vector.fromList <$>
                                                      (P.sepBy (makeProd <$$>
                                                      ((P.delay (makeType' resolveTycon resolveCon) <* P.spaces),
                                                      ((P.str "ref" *> P.pure true) <|> P.pure false)),
                                                       P.char #"," *> P.spaces))))

    in
        fun parseType resolveTycon resolveCon = makeType' resolveTycon resolveCon ()
        fun parseProd resolveTycon resolveCon = makeProd' resolveTycon resolveCon ()
    end

 val ctype = (P.any o List.map)
                (CType.all, fn ct =>
                 ct <$ token (CType.toString ct))

 val digits = P.many (P.nextSat (fn c => Char.isDigit c orelse c = #"~"))

 val parseIntInf = ((IntInf.fromString o String.implode) <$?> digits) <|> P.failCut "integer"

 val parseString = ((String.fromString o String.implode o List.concat) <$?>
       (P.char #"\"" *> (P.manyFailing(stringToken, P.char #"\"")) <* P.char #"\""))

 fun makeReal s = (case (RealX.make s) of NONE => NONE | x => x) handle Fail _ => NONE
 fun parseRealHelper sz = (makeReal <$?> (fn p => p) <$$> (String.implode <$>
       List.concat <$> P.each
       [P.many (P.nextSat (fn c => Char.isDigit c orelse c = #"~")),
        P.char #"." *> P.pure [#"."] <|> P.pure [],
        P.many (P.nextSat (fn c => Char.isDigit c orelse c = #"E" orelse c = #"~"))],
       P.pure sz))
 val parseReal = fn sz =>
    P.any
    [P.str "inf" *> P.pure (RealX.posInf sz),
     P.str "~inf" *> P.pure (RealX.negInf sz),
     parseRealHelper sz]

 val parseHex = P.fromReader (IntInf.scan(StringCvt.HEX, P.toReader P.next))

 val parseBool = true <$ token "true" <|> false <$ token "false"

 fun makeWord parseType int =
    if Tycon.isWordX parseType
       then P.pure (WordX.fromIntInf(int, (Tycon.deWordX parseType)))
       else P.fail "Invalid word"

 val parseWord8Vector = WordXVector.fromVector <$$>
      (P.pure {elementSize=WordSize.word8},
       P.char #"#" *> P.vector (parseHex >>= makeWord (Tycon.word WordSize.word8)))

 fun makeConstructor resolveCon (args, name) = {con = resolveCon name, args = args}

 fun constructor resolveCon resolveTycon = (makeConstructor resolveCon) <$$> ((parseProd resolveTycon resolveCon) <* P.spaces,
                                                                               ident <* P.spaces)

 fun makeDatatype resolveTycon(tycon, cons) =
 Datatype.T {
   tycon = resolveTycon tycon,
   cons = cons
 }

 fun makeDatatype' resolveCon resolveTycon = (makeDatatype resolveTycon) <$$>
                                                   ((P.spaces *> ident <* P.spaces <* symbol "="),
                                                   (Vector.fromList <$> P.sepBy1
                                                      ((constructor resolveCon resolveTycon) <* P.spaces,
                                                        P.char #"|" *> P.spaces)))

 fun parseDatatype resolveCon resolveTycon = P.spaces *> token "Datatypes:" *>
                                             Vector.fromList <$> P.many (makeDatatype' resolveCon resolveTycon)

 fun makeBase resolveVar =
     let

        val var = resolveVar <$> ident <* P.spaces

        val parseVar = P.failing (token "in" <|> token "exception" <|> token "val") *> var

        fun makeBaseObject x = Base.Object x

        val parseBaseObject = makeBaseObject <$> parseVar

        fun makeBaseSequenceSub (sequence, index)=
        Base.SequenceSub {
            index = index,
            sequence = sequence
        }

        val parseBaseSequenceSub = token "$" *> P.spaces *> parenOf (makeBaseSequenceSub <$$> (parseVar <* P.str "," <* P.spaces,
                                                                                           parseVar <* P.spaces)) <* P.spaces

        val parseBase = P.any[parseBaseSequenceSub, parseBaseObject]

        in
          parseBase
        end

fun parsePrimAppExp resolveTycon resolveCon resolveVar =
    let

       val var = resolveVar <$> ident <* P.spaces

       val varExp = P.failing (token "in" <|> token "exception" <|> token "val") *> var

       val parseConvention = CFunction.Convention.Cdecl <$ token "cdecl" <|>
                                        CFunction.Convention.Stdcall <$ token "stdcall"

       fun makeRuntimeTarget bytes ens mayGC maySwitch modifies readsSt writesSt =
                                  CFunction.Kind.Runtime ({bytesNeeded=bytes, ensuresBytesFree=ens,
                                  mayGC=mayGC, maySwitchThreads=maySwitch, modifiesFrontier=modifies,
                                  readsStackTop=readsSt, writesStackTop=writesSt})

       val parseRuntimeTarget = makeRuntimeTarget
                         <$> fromRecord "bytesNeeded" (optionOf P.uint)
                         <*> fromRecord "ensuresBytesFree" parseBool
                         <*> fromRecord "mayGC" parseBool
                         <*> fromRecord "maySwitchThreads" parseBool
                         <*> fromRecord "modifiesFrontier" parseBool
                         <*> fromRecord "readsStackTop" parseBool
                         <*> fromRecord "writesStackTop" parseBool
                         <* doneRecord

       val parseKind = CFunction.Kind.Impure <$ token "Impure" <|>
                                    CFunction.Kind.Pure <$ token "Pure" <|>
                                    token "Runtime" *> P.cut parseRuntimeTarget

       val parsePrototype = (fn x => x) <$$>
                     (fromRecord "args" (P.tuple ctype),
                      fromRecord "res" (optionOf ctype)) <* doneRecord

       val parseSymbolScope = P.any
                       [CFunction.SymbolScope.External <$ token "external",
                        CFunction.SymbolScope.Private <$ token "private",
                        CFunction.SymbolScope.Public <$ token "public"]

       val parseTarget = CFunction.Target.Indirect <$ symbol "<*>" <|>
                         CFunction.Target.Direct <$> ident

       fun makeFFI args conv kind prototype return symbolScope target =
                               Prim.ffi (CFunction.T
                              {args=args, convention=conv, kind=kind,
                               prototype=prototype, return=return, symbolScope=symbolScope,
                               target = target})

       val resolveFFI = token "FFI" *> P.cut( makeFFI
                            <$> fromRecord "args" (P.tuple (parseType resolveTycon resolveCon))
                            <*> fromRecord "convention" parseConvention
                            <*> fromRecord "kind" parseKind
                            <*> fromRecord "prototype" parsePrototype
                            <*> fromRecord "return" (parseType resolveTycon resolveCon)
                            <*> fromRecord "symbolScope" parseSymbolScope
                            <*> fromRecord "target" parseTarget
                            <* doneRecord)

       fun makeFFISym name cty symbolScope = Prim.ffiSymbol {name=name, cty=cty, symbolScope=symbolScope}

       val resolveFFISym = token "FFI_Symbol" *> P.cut( makeFFISym
                                      <$> fromRecord "name" ident
                                      <*> fromRecord "cty" (optionOf ctype)
                                      <*> fromRecord "symbolScope" parseSymbolScope
                                      <* doneRecord)

       fun resolvePrim p = case Prim.fromString p
                           of SOME p' =>  P.pure p'
                            | NONE => P.fail ("valid primitive, got " ^ p)

       fun makePrimApp(prim, args) = {args=args, prim=prim}
           in
              token "prim" *> P.spaces *> P.cut (makePrimApp <$$>
                             (P.any [ resolveFFI, resolveFFISym, (ident <* P.spaces >>= resolvePrim)],
                              P.spaces *> P.tuple varExp <* P.spaces))
           end

 fun makeBindStatement (var, ty, exp) =
 Statement.Bind {
    var = var,
    ty = ty,
    exp = exp
 }

 fun makeUpdateStatement (offset, base, value) =
 Statement.Update {
    base = base,
    offset = offset,
    value = value
 }

 fun parseStatements resolveCon resolveTycon resolveVar =
     let

     val var = resolveVar <$> ident <* P.spaces

     val parseVarExp = P.failing (token "in" <|> token "exception" <|> token "val") *> var

     val typedvar = (fn (x,y) => (x,y)) <$$>
        (SOME <$> var <|> token "_" *> P.pure(NONE),
         symbol ":" *> (parseType resolveTycon resolveCon) <* P.spaces)

     fun parseConstExp parseType = token "const" *> P.cut (
                                          case Type.dest parseType of
                                          Type.Word ws => Const.Word <$> (P.str "0x" *> parseHex >>=
                                          makeWord (Tycon.word ws)) <|> P.failCut "word"
                                        | Type.Real rs => Const.Real <$> parseReal rs <|> P.failCut "real"
                                        | Type.IntInf => Const.IntInf <$> parseIntInf <|> P.failCut "integer"
                                        | Type.CPointer => Const.null <$ token "NULL" <|> P.failCut "null"
                                        | Type.Object _  =>
                                          (* assume it's a word8 vector *)
                                          P.any
                                          [Const.string <$> parseString,
                                          Const.wordVector <$> parseWord8Vector,
                                          P.failCut "string constant"]
                                        | _ => P.fail "constant" )



     fun makeInjectExp (variant, sum) = {sum = sum, variant = variant}
     val parseInjectExp = token "inj" *> P.spaces *> makeInjectExp <$$>
                                                                   (parenOf(parseVarExp) <* token ":" <* P.spaces,
                                                                    P.spaces *> resolveTycon <$> ident <* P.spaces)

     fun makeObjectExp (con, args) = {con = con, args = args}

     fun makeObjectExp' () = makeObjectExp <$$> (((P.spaces *> token "tuple" *> P.spaces *> P.pure(NONE)) <|>
                                                  (SOME <$> (resolveCon <$> ident <* P.spaces))),
                                                 P.spaces *> P.tuple parseVarExp <|> P.pure (Vector.new0 ()) <* P.spaces)

     val parseObjectExp = token "new" *> P.spaces *> P.cut(makeObjectExp' ())

     fun makeSelectExp (offset, base) = {offset = offset, base = base}
     val parseSelectExp = token "sel" *> P.spaces *> P.cut(makeSelectExp <$$> (P.uint <* P.spaces,
                                                                               parenOf (makeBase resolveVar)))

     fun parseExpressions parseType = P.any [Exp.Const   <$>   parseConstExp parseType,
                                             Exp.Inject  <$>   parseInjectExp,
                                             Exp.Object  <$>   parseObjectExp,
                                             Exp.PrimApp <$>  (parsePrimAppExp resolveTycon resolveCon resolveVar),
                                             Exp.Select  <$>   parseSelectExp,
                                             Exp.Var     <$>   parseVarExp
                                            ]

     val parseBindStatement = makeBindStatement <$> (P.spaces *> token "val" *> P.spaces *>
                                                    (typedvar >>= (fn (var, ty) =>
                                                    (symbol "=" *> parseExpressions ty <* P.spaces)
                                                    >>= (fn exp => P.pure (var, ty, exp)))))

     val parseProfileStatement = Statement.Profile <$> (P.spaces *> token "prof" *> P.spaces *>
                                                       (ProfileExp.Enter <$ token "Enter" <|>
                                                        ProfileExp.Leave <$ token "Leave") <*>
                                                        P.cut ((SourceInfo.fromC o String.implode) <$>
                                                        P.manyCharsFailing(P.char #"\n") <* P.char #"\n" <* P.spaces))

     val parseUpdateStatement = P.spaces *> token "upd" *> P.spaces *> token "sel" *> P.spaces *>
                                makeUpdateStatement <$$$> (P.uint <* P.spaces,
                                                           parenOf (makeBase resolveVar),
                                                           P.spaces *> P.str ":=" *> P.spaces *>parseVarExp <* P.spaces)

     val parseStatements = P.any [parseBindStatement,
                                  parseProfileStatement,
                                  parseUpdateStatement]

     in
        parseStatements
     end

 fun parseGlobals resolveCon resolveTycon resolveVar =
    let
        fun parseGlobals' () = P.spaces *> token "Globals:" *> Vector.fromList <$>
                                    P.many (parseStatements resolveCon resolveTycon resolveVar)
    in
        parseGlobals' ()
    end

 fun parseMain resolveFunc = P.spaces *> token "Main:" *> resolveFunc <$> ident <* P.spaces

 fun makeFunction name args returns raises label blocks =
 Function.new {
   args = args,
   returns = returns,
   name = name,
   raises = raises,
   mayInline = false,
   start = label,
   blocks = blocks
 }

 fun parseFunctions resolveCon resolveTycon resolveVar resolveFunc resolveLabel =
     let
        val functionName =  P.spaces *> symbol "fun" *> resolveFunc <$> ident <* P.spaces

        val var = resolveVar <$> ident <* P.spaces

        (*val functionLabel = P.spaces *> symbol "=" *> P.spaces *> resolveLabel <$> ident <* P.spaces <* token "()"*)

        val functionLabel = P.spaces *> symbol "=" *> P.spaces *> P.str "goto" *> P.spaces *>
                                              resolveLabel <$> ident <* P.spaces <* token "()"

        val label' = resolveLabel <$> ident <* P.spaces

        val con' = P.spaces *> resolveCon <$> ident <* P.spaces

        val blockLabel = P.spaces *> resolveLabel <$> ident

        val typedvar = (fn (x,y) => (x,y)) <$$>
                                           (var,
                                            symbol ":" *> P.spaces *> (parseType resolveTycon resolveCon) <* P.spaces)

        val args = P.spaces *> (P.tuple typedvar <|> P.pure (Vector.new0 ())) <* P.spaces

        val vars = P.spaces *> (P.tuple var <|> P.pure (Vector.new0 ())) <* P.spaces

        fun makeConCases var (cons, def) =
           {test = var,
            cases = Cases.Con cons,
            default = def}

        fun makeWordCases var s (wds, def) =
            {test=var,
              cases=Cases.Word (case s of
                8  => WordSize.word8
              | 16 => WordSize.word16
              | 32 => WordSize.word32
              | 64 => WordSize.word64
              | _  => raise Fail "makeWordCases" (* can't happen *)
                 , wds),
              default=def}

        fun makePat(con, exp) = P.pure (con, exp)

        fun makeCaseWord size (int, exp) = case size of
               8  => P.pure ((WordX.fromIntInf(int, WordSize.word8)), exp)
             | 16 => P.pure ((WordX.fromIntInf(int, WordSize.word16)), exp)
             | 32 => P.pure ((WordX.fromIntInf(int, WordSize.word32)), exp)
             | 64 => P.pure ((WordX.fromIntInf(int, WordSize.word64)), exp)
             | _  => P.fail "valid word size for cases (8, 16, 32 or 64)"

        val defaultCase = P.spaces *> P.optional(P.char #"|" *> P.spaces *> token "_" *> P.spaces *> token
                                   "=>" *> P.spaces *> label')

        val makeTransferCase = P.str "case" *> P.optional P.uint <* P.many1 P.space >>= (fn size => P.cut(
                               var <* token "of" <* P.spaces >>= (fn test =>
                               case size of
                                         NONE => makeConCases test <$$>
                                                (casesOf(makePat, con', label'),
                                                 defaultCase)
                                       | SOME s => makeWordCases test s <$$>
                                                  (casesOf(makeCaseWord s, P.str "0x" *> parseHex,
                                                   label'),
                                                   defaultCase))))

        val parseTransferCase = Transfer.Case <$> makeTransferCase

        fun makeTransferGoto dst args =
        Transfer.Goto {
          dst = dst,
          args = args
        }

        val parseTransferGoto = P.spaces *> P.str "goto" *> P.spaces *> makeTransferGoto <$> blockLabel
                                                                                         <*> vars

        fun makeTransferArith (ty, success, {prim, args}, overflow) =
        Transfer.Arith {
          prim = prim,
          args = args,
          overflow = overflow,
          success = success,
          ty = ty
        }

        val parseTransferArith = P.str "arith" *> P.spaces *> makeTransferArith <$$$$>
                                                                        (parseType resolveTycon resolveCon <* P.spaces,
                                                                         label',
                                                                         parenOf(parsePrimAppExp resolveTycon resolveCon resolveVar),
                                                                         P.spaces *> P.str "handle Overflow => " *> label' <* P.spaces)

        fun makeReturnNonTail cont (handler) =
        Return.NonTail {
          cont = cont,
          handler = case handler of
                                "raise" => Handler.Caller
                              | "dead" => Handler.Dead
                              | _ => Handler.Handle (resolveLabel handler)
        }

        fun parseReturnNonTail cont = makeReturnNonTail cont <$> (P.str "handle _ => " *> ident <* P.spaces)

        fun getReturn return = case return of
                                          "dead"   => P.pure(Return.Dead)
                                        | "return" => P.pure(Return.Tail)
                                        | _        => parseReturnNonTail (resolveLabel return)

        fun makeTransferCall args func (return) =
        Transfer.Call {
          args = args,
          func = func,
          return = return
        }

        val parseTransferCall = P.spaces *> P.str "call" *> P.spaces *> ident <* P.spaces >>= (fn return =>
                                symbol "(" *> resolveFunc <$> ident <* P.spaces >>= (fn func =>
                                vars <* symbol ")" <* P.spaces >>= (fn argus =>
                                makeTransferCall argus func <$> (getReturn return))))

        val parseTransferBug = P.spaces *> P.str "bug" *> P.spaces *> P.pure(Transfer.Bug) <* P.spaces

        fun makeTransferRuntime (return , {prim, args}) =
        Transfer.Runtime {
           args = args,
           prim = prim,
           return = return
        }

        val parseTransferRuntime = P.spaces *> P.str "runtime" *> P.spaces *>
                                   makeTransferRuntime <$$>
                                  (label' <* P.spaces,
                                   parenOf (parsePrimAppExp resolveTycon resolveCon resolveVar))

        fun makeTransferReturn vars = Transfer.Return vars

        val parseTransferReturn = P.spaces *> P.str "return" *> P.spaces *> makeTransferReturn <$> (vars <* P.spaces)

        fun makeTransferRaise vars = Transfer.Raise vars

        val parseTransferRaise = P.spaces *> P.str "raise" *> P.spaces *> makeTransferRaise <$> (vars <* P.spaces)

        val parseTransfer = P.any [parseTransferArith,
                                   parseTransferBug,
                                   parseTransferCall,
                                   parseTransferCase,
                                   parseTransferGoto,
                                   parseTransferRaise,
                                   parseTransferReturn,
                                   parseTransferRuntime]

        fun makeBlock label args statements transfer =
        Block.T {
           args = args,
           label = label,
           statements = statements,
           transfer = transfer
        }

        val parseBlock = P.spaces *> P.str "block:" *> P.spaces *>
                         makeBlock
                         <$> blockLabel
                         <*> args <* P.spaces
                         <*> (Vector.fromList <$> P.many (parseStatements resolveCon resolveTycon resolveVar))
                         <*> parseTransfer

        val makeFunction' = makeFunction
                           <$> functionName
                           <*> args <* symbol ":" <* P.spaces
                           <*> fromRecord "returns" (optionOf (P.tuple (parseType resolveTycon resolveCon) <|> P.pure (Vector.new0 ())))
                           <*> fromRecord "raises" (optionOf (P.tuple (parseType resolveTycon resolveCon) <|> P.pure (Vector.new0 ())))
                           <*  doneRecord
                           <*> functionLabel
                           <*> (Vector.fromList <$> P.manyFailing(parseBlock, P.peek(functionName)))

        val parseFunction' = P.spaces *> token "Functions:" *> P.many makeFunction'

    in
      parseFunction'
    end

 fun makeProgram ( datatypes, globals, main, functions ) =
 Program.T {
   datatypes = datatypes,
   functions = functions,
   globals = globals,
   main = main
 }

 val program : Program.t Parse.t =
    let
       fun strip_unique s  = case P.parseString
          (String.implode <$> P.manyCharsFailing(
             P.char #"_" *> P.many1 (P.nextSat Char.isDigit) *> P.failing P.next),
           s) of Result.Yes s' => s'
               | Result.No _ => s
       val resolveCon0 = makeNameResolver(Con.newString o strip_unique)
       fun resolveCon ident =
          case List.peek ([Con.falsee, Con.truee, Con.overflow, Con.reff], fn con =>
                          ident = Con.toString con) of
             SOME con => con
           | NONE => resolveCon0 ident
       val resolveTycon0 = makeNameResolver(Tycon.newString o strip_unique)
       fun resolveTycon ident =
          case ident of
               "bool" => Tycon.bool
             | "exn" => Tycon.exn
             | _ => resolveTycon0 ident

       val resolveVar = makeNameResolver(Var.newString o strip_unique)
       val resolveFunc = makeNameResolver(Func.newString o strip_unique)
       val resolveLabel = makeNameResolver(Label.newString o strip_unique)
    in
       P.compose(skipComments (),
       (makeProgram <$$$$>
           (parseDatatype resolveCon resolveTycon,
            parseGlobals resolveCon resolveTycon resolveVar,
            parseMain resolveFunc,
            parseFunctions resolveCon resolveTycon resolveVar resolveFunc resolveLabel
            (* failing next to check for end of file *)
            <* P.spaces <* (P.failing P.next <|> P.failCut "End of file"))))
    end

 end
