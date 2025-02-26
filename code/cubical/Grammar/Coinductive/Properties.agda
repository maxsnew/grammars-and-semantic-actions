{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Equalizer Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Coinductive.Indexed Alphabet
open import Grammar.Inductive.Functor Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓX : Level

module _ {X : Type ℓX} (F : X → Functor X) where
  open StrongEquivalence

  rollν≅ : ∀ x → ν F x ≅ ⟦ F x ⟧ (ν F)
  rollν≅ x .fun = unrollν' F x
  rollν≅ x .inv = rollν F x
  rollν≅ x .sec = refl
  rollν≅ x .ret = refl
