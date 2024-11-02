open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Test (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Grammar Alphabet
open import Term.Base Alphabet
open import SemanticAction.Base Alphabet

private
  variable
    A : Type _
    g : Grammar _

runParser : (parser : string ⊢ g) (s : String) → g s
runParser parser s = (parser ∘g ⌈w⌉→string {w = s}) s (internalize s)

runParserΔ : (parser : string ⊢ Δ A) (s : String) → A
runParserΔ parser s = runParser parser s .fst

