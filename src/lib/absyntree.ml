(* Convert abstract syntax trees to generic trees of list of string *)

open Absyn

(* Helper functions *)

(* Format arguments according to a format string resulting in a string *)
let sprintf = Format.sprintf

(* Concatenate the lines of text in the node *)
let flat_nodes tree =
  Tree.map (String.concat "\n") tree

(* Build a singleton tree from a string *)
let mktr s = Tree.mkt [s]


(* Convert an expression to a generic tree *)
let rec tree_of_exp exp =
  match exp with
  | BoolExp x                 -> mktr (sprintf "BoolExp %b" x) []
  | IntExp x                  -> mktr (sprintf "IntExp %i" x) []
  | RealExp x                 -> mktr (sprintf "RealExp %f" x) []
  | WhileExp (t, b)           -> mktr "WhileExp" [tree_of_lexp t; tree_of_lexp b]
  | BreakExp                  -> mktr "BreakExp" []

(* Convert an anotated expression to a generic tree *)
and tree_of_lexp (_, x) = tree_of_exp x