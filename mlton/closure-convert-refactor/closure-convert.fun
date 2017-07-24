(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor ClosureConvertRefactor (S: CLOSURE_CONVERT_STRUCTS): CLOSURE_CONVERT =
struct

open S

(* CFAs *)
structure IntersectCFA = IntersectCFA(S)
structure OrigCFA = OrigCFA(S)
structure SynKnownCFA = SynKnownCFA(S)
structure TyCFA = TyCFA(S)
structure ZeroCFA = ZeroCFA(S)
structure mCFA = GenCFA(struct
                           structure Sxml = Sxml
                           structure Alloc = MAllocator(S)
                        end)
val cfaRef = ref (fn _ => Error.bug "ClosureConvert.cfa unset")
val cfaString = ref "<cfa>"
val cfaGet = fn () => !cfaString
local
   fun set string cfa = 
         (cfaRef := cfa;
         cfaString := string)
   open Parse
   infix 1 <|> >>=
   infix 2 <&>
   infix  3 <*> <* *>
   infixr 4 <$> <$$> <$$$> <$

   fun cfaRdrs () = any (List.map (
      [IntersectCFA.scan,
       SynKnownCFA.scan,
       mCFA.scan,
       TyCFA.scan,
       ZeroCFA.scan,
       OrigCFA.scan], 
      fn f => f (delay cfaRdrs)))
in
   fun cfaSet s = parseString(set s <$> (cfaRdrs () <* failing next), s)
end
val _ = List.push (Control.indirectFlags, {flag = "cc-cfa", get = cfaGet, set = cfaSet})
val _ = cfaSet "synkwn(tycfa)"

(* Transforms *)
structure TyTransform = TyTransform(S)
structure UnifTransform = UnifTransform(S)
val transRef = ref (fn _ => Error.bug "ClosureConvert.trans unset")
val transString = ref "<trans>"
val transGet = fn () => !transString
val transSet =
   let
      val transRdrs =
         TyTransform.scan ::
         UnifTransform.scan ::
         nil

      fun transRdrRec charRdr strm0 =
         let
            fun loop transRdrs =
               case transRdrs of
                  [] => NONE
                | transRdr::transRdrs =>
                     (case transRdr transRdrRec charRdr strm0 of
                         NONE => loop transRdrs
                       | SOME (trans, strm') => SOME (trans, strm'))
         in
            loop transRdrs
         end
   in
      fn s =>
      case transRdrRec Substring.getc (Substring.full s) of
         NONE => Result.No s
       | SOME (trans, ss') =>
            if Substring.isEmpty ss'
               then (transRef := trans;
                     transString := s;
                     Result.Yes ())
               else Result.No s
   end
val _ = List.push (Control.indirectFlags, {flag = "cc-trans", get = transGet, set = transSet})
val _ = transSet "tytrans(g:true,s:true)"

fun closureConvert (program: Sxml.Program.t): Ssa.Program.t =
   let
      val Sxml.Program.T {body, ...} = program

      val cfa =
         Control.trace (Control.Pass, "cfa: " ^ !cfaString) (!cfaRef)

      val {cfa, destroy = destroyCFA, ...} =
         cfa {program = program}

      val _ =
         Control.diagnostics
         (fn display =>
          let
             val {get, set, rem} =
                Property.getSetOnce
                (Sxml.Var.plist,
                 Property.initRaise ("ClosureConvert.get", Sxml.Var.layout))
             val _ =
                Sxml.Exp.foreachBoundVar
                (body, fn (var, _, ty) => set (var, ty))
             val _ =
                Sxml.Exp.foreachPrimExp
                (body, fn (res, resTy, exp) =>
                 case exp of
                    Sxml.PrimExp.App {func, arg} =>
                       let
                          val func = Sxml.VarExp.var func
                          val arg = Sxml.VarExp.var arg
                          val lambdas =
                             cfa {arg = arg,
                                  argTy = get arg,
                                  func = func,
                                  res = res,
                                  resTy = resTy}
                          val lambdas =
                             List.insertionSort
                             (lambdas, fn (lam1, lam2) =>
                              String.<= (Sxml.Var.toString (Sxml.Lambda.arg lam1),
                                         Sxml.Var.toString (Sxml.Lambda.arg lam2)))
                          val lambdasCard =
                             Int.layout (List.length lambdas)
                          fun layoutLam lam =
                             Layout.seq
                             [Layout.str "fn ",
                              Sxml.Var.layout (Sxml.Lambda.arg lam)]
                          val lambdas =
                             Layout.seq [Layout.str "{",
                                         (Layout.fill o Layout.separateRight)
                                         (List.map (lambdas, layoutLam), ","),
                                         Layout.str "}"]
                          val call =
                             (Layout.str o String.concat)
                             ["val ",
                              Sxml.Var.toString res,
                              " = ",
                              Sxml.Var.toString func,
                              " ",
                              Sxml.Var.toString arg]
                       in
                          (display o Layout.seq)
                          [Layout.str "|cfa(", call, Layout.str ")| = ", lambdasCard];
                          (display o Layout.align)
                          [Layout.seq [Layout.str "cfa(", call, Layout.str ") ="],
                           Layout.indent (lambdas, 3)]
                       end
                  | _ => ())
             val _ =
                Sxml.Exp.foreachBoundVar
                (body, fn (var, _, _) => rem var)
          in
             ()
          end)

      val transform =
         Control.trace (Control.Pass, "trans: " ^ !transString) (!transRef)

      val {program, destroy = destroyTransform, ...} =
         transform {program = program, cfa = cfa}

      val _ = destroyCFA ()
      val _ = destroyTransform ()
      val _ = Ssa.Program.clear program
   in
      program
   end

end
