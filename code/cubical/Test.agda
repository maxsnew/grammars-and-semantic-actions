open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Test (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Maybe
import Cubical.Data.Sum as Sum

open import Grammar Alphabet
import Grammar.Maybe Alphabet as Grammar
open import Term.Base Alphabet
open import SemanticAction.Base Alphabet
open import ParserCombinator.Base Alphabet

private
  variable
    A : Type _
    g : Grammar _

opaque
  unfolding _⊗_ literal

  internalize' : (s : String) → string s
  internalize' [] = NIL [] ε-intro
  internalize' (x ∷ s) = CONS (x ∷ s) ((([ x ] , s) , refl) , ((x , refl) , internalize' s))

runParser : (parser : string ⊢ g) (s : String) → g s
--runParser parser s = (parser ∘g ⌈w⌉→string {w = s}) s (internalize s)
runParser parser s = parser s (internalize' s)

runParserΔ : (parser : string ⊢ Δ A) (s : String) → A
runParserΔ parser s = runParser parser s .fst

opaque
  unfolding _⊗_ _⊕_

  runWeakParser : (parser : WeakParser g) (s : String) → Maybe (g s)
  runWeakParser parser s = Sum.rec just (λ _ → nothing) (runParser (finish parser) s)

  runWeakParserΔ : (parser : WeakParser (Δ A)) (s : String) → Maybe A
  runWeakParserΔ parser s = map-Maybe fst (runWeakParser parser s)

