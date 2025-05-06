{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Equalizer.Base Alphabet isSetAlphabet
open import Grammar.Product.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Inductive.Indexed Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable ℓA ℓB ℓX : Level

module _ {X : Type ℓX} {{monStr : MonoidalStr}} (F : X → Functor X) where
  open MonoidalStr monStr
  open StrongEquivalence

  unroll≅ : ∀ x → μ F x ≅ ⟦ F x ⟧ (μ F)
  unroll≅ x .fun = unroll F x
  unroll≅ x .inv = roll
  unroll≅ x .sec = refl
  unroll≅ x .ret =
    equalizer-ind
      F
      (λ x → μ F x)
      (λ x → roll ∘g unroll F x)
      (λ _ → id)
      (λ x → refl)
      x
