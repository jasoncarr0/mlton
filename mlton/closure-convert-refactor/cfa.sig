(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature CFA_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature CFA =
   sig
      include CFA_STRUCTS

      structure Config:
         sig
            type t
         end

      type t = {program: Sxml.Program.t} ->
               {caseUsed: {test: Sxml.Var.t,
                           con: Sxml.Con.t} ->
                   bool,
                cfa: {arg: Sxml.Var.t,
                      argTy: Sxml.Type.t,
                      func: Sxml.Var.t,
                      res: Sxml.Var.t,
                      resTy: Sxml.Type.t} ->
                   Sxml.Lambda.t list,
                destroy: unit -> unit,
                knownCon: {res: Sxml.Var.t} ->
                   {arg: Sxml.VarExp.t option,
                    con: Sxml.Con.t} option,
                varUsed: {var: Sxml.Var.t} ->
                   bool}

      val cfa: {config: Config.t} -> t

      val scan: t Parse.t -> t Parse.t 
end
