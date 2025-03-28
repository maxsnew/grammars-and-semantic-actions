open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Empty as Empty
open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Unambiguous Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Properties Alphabet
open import Term.Base Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  unambiguous-literal : unambiguous ＂ c ＂
  unambiguous-literal = unambiguous⊕ᴰ (Alphabet .snd) unambiguous-char c

  module _ (c' : ⟨ Alphabet ⟩) where
    -- Properties for literals that are useful in establishing
    -- sequential ambiguity axioms
    module _ where
      opaque
        unfolding _&_ literal ⊥
        same-literal : ＂ c ＂ & ＂ c' ＂ ⊢ ⊕[ _ ∈ (c ≡ c') ] ＂ c ＂
        same-literal w (p , p') = c≡c' , p
          where
          c≡c' : c ≡ c'
          c≡c' = cons-inj₁ ((sym p) ∙ p')

        opaque
          unfolding _⊗_
          same-first : startsWith c & startsWith c' ⊢ ⊕[ _ ∈ (c ≡ c') ] startsWith c
          same-first w ((s , pc , str) , (s' , pc' , _)) = c≡c' , s , (pc , str)
            where
            c≡c' : c ≡ c'
            c≡c' =
              cons-inj₁
              (cong (_++ s .fst .snd) (sym pc)
              ∙ (sym (s .snd)
              ∙ (s' .snd))
              ∙ cong (_++ s' .fst .snd) pc')

    disjoint-literals : (c ≡ c' → Empty.⊥) → disjoint ＂ c ＂ ＂ c' ＂
    disjoint-literals c≢c' = ⊕ᴰ-elim (Empty.rec ∘ c≢c') ∘g same-literal
