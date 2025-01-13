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
open import Term.Base Alphabet

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ {A : Type ℓ} (F : A → Functor A) where
  open StrongEquivalence

  rollν≅ : ∀ a → ν F a ≅ ⟦ F a ⟧ (ν F)
  rollν≅ a .fun = unrollν' F a
  rollν≅ a .inv = rollν F a
  rollν≅ a .sec = refl
  rollν≅ a .ret = refl
