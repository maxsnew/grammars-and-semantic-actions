open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.String.Properties Alphabet
open import Term.Base Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    unambiguous-literal : unambiguous ＂ c ＂
    unambiguous-literal = ans
      where
      opaque
        unfolding literal
        ans : unambiguous ＂ c ＂
        ans = EXTERNAL.isLang→unambiguous isFinSetAlphabet λ w → isSetString _ _
