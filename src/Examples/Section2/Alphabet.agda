module Examples.Section2.Alphabet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet

data Alphabet' : Type where
  a b c : Alphabet'

Alphabet'Rep : Iso Alphabet' (Fin 3)
Alphabet'Rep = iso
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

isSetAlphabet' : isSet Alphabet'
isSetAlphabet' =
  isSetRetract (Alphabet'Rep .fun) (Alphabet'Rep .inv)
               (Alphabet'Rep .leftInv) isSetFin

Alphabet : hSet ℓ-zero
Alphabet = Alphabet' , isSetAlphabet'

isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩
isFinSetAlphabet = EquivPresIsFinSet (isoToEquiv (invIso Alphabet'Rep)) isFinSetFin
