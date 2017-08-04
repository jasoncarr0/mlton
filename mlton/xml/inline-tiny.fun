(* Copyright (C) 2017 Jason Carr.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

 (*
  * Inline very small functions to get more precise analyses
  *)
functor InlineTiny (S: XML_TRANSFORM_STRUCTS): XML_TRANSFORM = 
struct

open S
open Dec PrimExp

fun shouldInline (lam: Lambda.t): bool =
   if Lambda.mayInline lam then
      let
         val {body, ...} = Lambda.dest lam
      (* look for a function that is a series of selects/tuples
       * followed by one to zero primexps *)
         val decs = Exp.decs body
         fun isGroupingDec dec = 
            case dec of
                MonoVal {exp, ...} =>
                (case exp of
                    Select _ => true
                  | Tuple _ => true
                  | Var _ => true
                  | Const _ => true
                  | _ => false)
                 | _ => false
         val (_, decsRest) = List.splitPrefix (decs, isGroupingDec)

      in 
         case decsRest of
             [] => true
           | (MonoVal {exp=x, ...}) :: [] => (case x of
               PrimApp _ => true
             | Raise _ => true
             | _ => false)
           | _ => false
      end
   else false

(* for each function, loop and ensure it occurs only in an app position *)
(* check if it's small enough to inline or if it has only one occurence *)
fun transform (Program.T {body, datatypes, overflow}): Program.t =
   let
      datatype occurence = 
         FO 
       | HO
      val {get = callInfo: Var.t -> occurence ref,
           destroy = destroyCallInfo} = 
         Property.destGet (Var.plist, Property.initFun (fn _ => ref FO))
      val {get = lambdaInfo: Var.t -> Lambda.t, set = setLambdaInfo,
           destroy = destroyLambdaInfo} =
         Property.destGetSetOnce (Var.plist, 
            Property.initRaise ("inlineTiny lambdaInfo", Var.layout))
     

         

      fun setHO varExp =
         callInfo (VarExp.var varExp) := HO

      fun loopExp (exp: Exp.t) =
         List.foreach (Exp.decs exp, loopDec)
      and loopDec (dec: Dec.t) =
         case dec of
            Fun {decs, ...} =>
               Vector.foreach (decs, loopLambda)
          | MonoVal {var, ty, exp} => 
               (case exp of
                   Lambda lambda => loopLambda {var=var, ty=ty, lambda=lambda}
                 | _ => loopPrimExp exp)
          | _ => ()
      and loopLambda {var, ty=_, lambda} = 
         (setLambdaInfo (var, lambda);
         loopExp (Lambda.body lambda))
      and loopPrimExp exp = 
         (case exp of
            App {arg, ...} =>
               setHO arg
          | ConApp {arg, ...} =>
               Option.foreach (arg, setHO)
          | Case {cases, default, ...} =>
               (Cases.foreach (cases, loopExp);
                Option.foreach (default, fn (e, _) => loopExp e))
          | Handle {try, handler, ...} =>
               (loopExp try;
               loopExp handler)
          | PrimApp {args, ...} =>
               Vector.foreach (args, setHO)
          | Tuple vars =>
               Vector.foreach (vars, setHO)
          | _ => ())
     
      val _ = loopExp body

      val _ =
         Control.diagnostics
            (fn display => 
               Exp.foreachBoundVar
               (body, fn (var, _, _) =>
                  let 
                     val lam = lambdaInfo var 
                     val _ = display (Lambda.layout lam)
                     val _ = (display o Layout.seq)
                        [(Bool.layout (shouldInline lam)),
                         Layout.str ", ",
                         case !(callInfo var) of
                             HO => Layout.str "HO"
                           | FO => Layout.str "FO"]

                  in
                     ()
                  end
                  handle _ => ()))

      fun inline {var, ty, func, arg} = 
         let
            val lam = lambdaInfo func
            val {arg=form, argType=formTy, body, ...} = Lambda.dest lam
            val decs = Exp.decs body
            val res = Exp.result body
            val setForm = MonoVal {var=form, ty=formTy,
               exp=PrimExp.Var (VarExp.mono arg)}
            val setRes = MonoVal {var=var, ty=ty,
               exp=PrimExp.Var res}
         in
            setForm :: decs @ setRes :: []
         end

      fun reduceExp exp = 
         case Exp.dest exp of {decs, result} =>
            Exp.make {decs = reduceDecs decs,
                      result = result}
      and reduceDecs decs: Dec.t list =
         case decs of 
             [] => []
           | dec :: decs =>
                (case dec of
                  Fun {decs=fundecs, tyvars} =>
                     [Fun {decs=Vector.map (fundecs, 
                              fn {var, ty, lambda} =>
                                 let
                                    val lam' = reduceLambda lambda
                                 in 
                                    {var=var, ty=ty, lambda=lam'}
                                 end),
                           tyvars=tyvars}]
                 | MonoVal {var, ty, exp} =>
                   reduceMonoVal {var=var, ty=ty, exp=exp}
                 | _ => [dec]) @ reduceDecs decs
      and reduceMonoVal (dec as {var, ty, exp}) =
         (case exp of
             App {func, arg} =>
                (let
                  val func = VarExp.var func
                  val arg = VarExp.var arg
                  val _ = Control.diagnostics 
                     (fn display => (display o Layout.seq)
                        [Layout.str "Trying ",
                         Var.layout func,
                         Layout.str " ",
                         Var.layout arg,
                         Layout.str " with ",
                         Layout.str (case !(callInfo func) of
                             HO => "HO"
                           | FO => "FO"),
                         Layout.str " and ",
                         Bool.layout (shouldInline (lambdaInfo func))])
                in
                   if !(callInfo func) = FO andalso 
                   shouldInline (lambdaInfo func)
                     then inline {var=var, ty=ty, func=func, arg=arg}
                   else [MonoVal dec]
                end
                handle _ => [MonoVal dec]) (* higher order application *)
           | x => [MonoVal {var=var, ty=ty, exp=(case x of
                   Handle {try, catch, handler} =>
                      Handle {try=reduceExp try, catch=catch, handler=reduceExp handler}
                 | Case {test, cases, default} =>
                      Case {test=test, 
                            cases=Cases.map (cases, reduceExp), 
                            default=Option.map (default, 
                              fn (exp, reg) => (reduceExp exp, reg))}
                 | Lambda lam => Lambda (reduceLambda lam)
                 | _ => x)}])
      and reduceLambda lambda = 
         let
            val {arg, argType, mayInline, body} = Lambda.dest lambda
         in
            Lambda.make 
               {arg=arg,
                argType=argType,
                body=(reduceExp body),
                mayInline=mayInline}
         end
      
      val result = Program.T 
         {body=reduceExp body,
          datatypes=datatypes,
          overflow=overflow}
      
      val _ = destroyCallInfo
      val _ = destroyLambdaInfo
   in
      result
   end
end
