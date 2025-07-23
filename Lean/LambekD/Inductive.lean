import LambekD.Grammar
import LambekD.Monoidal
import LambekD.Disjunction
import LambekD.Conjunction

import Lean
open Lean Elab Meta PrettyPrinter Delaborator

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

declare_syntax_cat dsl_constructor_ty
syntax sepBy(term , "⊸"): dsl_constructor_ty

declare_syntax_cat dsl_constructor
syntax ident ":" dsl_constructor_ty : dsl_constructor

declare_syntax_cat index
syntax "(" ident ":" term ")" : index

syntax "data" ident index* "where" dsl_constructor* : command

macro_rules
| `(command|data $name $indices* where $constructors*) => do
  let mut idxs := #[]
  for i in indices do
    match i with
    | `(index|($idxName:ident : $idxType:term)) =>
      -- idxs := idxs.push (idxName.getId, idxType)
      idxs := idxs.push (← `(bracketedBinder|($idxName:ident : $idxType)))
    | _ => Macro.throwUnsupported
  let mut ctors := #[]
  for c in constructors do
    match c with
    | `(dsl_constructor|$ctorName:ident : $ctorType:dsl_constructor_ty) =>
      ctors := sorry -- ctors.push (← `(ctor|$ctorName : $leanType))
    | _ => Macro.throwUnsupported

  `(inductive $name $idxs* : SemGrammar where $ctors*)


-- data B (A : SemGrammar) where
--   nil : Epsilon ⊸ A
--   cons : B ⊸ A ⊸ A
