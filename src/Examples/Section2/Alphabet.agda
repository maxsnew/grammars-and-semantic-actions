{-# OPTIONS --erased-cubical #-}
module Examples.Section2.Alphabet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet

data Alphabet : Type where
  a b c : Alphabet

@0 AlphabetRep : Iso Alphabet (Fin 3)
AlphabetRep = iso
  (λ where
    a → fromℕ 0
    b → fromℕ 1
    c → fromℕ 2)
  (λ where
    fzero → a
    (fsuc fzero) → b
    (fsuc (fsuc fzero)) → c)
  (λ where
    fzero → refl
    (fsuc fzero) → refl
    (fsuc (fsuc fzero)) → refl)
  (λ where
    a → refl
    b → refl
    c → refl)

open Iso

@0 isSetAlphabet : isSet Alphabet
isSetAlphabet =
  isSetRetract (AlphabetRep .fun) (AlphabetRep .inv)
               (AlphabetRep .leftInv) isSetFin

-- Alphabet : hSet ℓ-zero
-- Alphabet = Alphabet' , isSetAlphabet'

@0 isFinSetAlphabet : isFinSet Alphabet
isFinSetAlphabet = EquivPresIsFinSet (isoToEquiv (invIso AlphabetRep)) isFinSetFin
