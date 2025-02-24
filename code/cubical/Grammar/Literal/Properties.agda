open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.List

open import Grammar Alphabet
open import Grammar.HLevels.Properties Alphabet
open import Term.Base Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  module _ (c' : ⟨ Alphabet ⟩) where
    opaque
      unfolding _&_ literal
      same-literal : ＂ c ＂ & ＂ c' ＂ ⊢ ⊕[ x ∈ (c ≡ c') ] ＂ c ＂
      same-literal w (p , p') = c≡c' , p
        where
        c≡c' : c ≡ c'
        c≡c' = cons-inj₁ ((sym p) ∙ p')

module _ (c : ⟨ Alphabet ⟩) where
  unambiguous-literal : unambiguous ＂ c ＂
  unambiguous-literal = EXTERNAL.isLang→unambiguous (isLangLiteral c)
