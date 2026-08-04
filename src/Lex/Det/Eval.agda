{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Lex.Det.Eval
  (Alphabet : hSet ℓ-zero)
  where

open import Cubical.Data.Unit

open import Parser.Base Alphabet
open import Parser.RecursiveDescent Alphabet using (unfoldRecursiveDescentDefs)
import Grammar.Greedy.Automata Alphabet as GA
open import Lex.Det.Base Alphabet using (runLex ; ruleAction)

opaque
  unfolding unfoldParserDefs unfoldRecursiveDescentDefs GA.⟜-Trace-disj runLex ruleAction

  eval-lex-det : Unit
  eval-lex-det = tt
