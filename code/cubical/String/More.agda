open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.More (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.List
open import Cubical.Data.FinSet

open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Grammar.KleeneStar Alphabet
open import Helper

-- Some resources for reasoning internally about strings

-- why is this in String.More and not Grammar.Something ?
char : Grammar ℓ-zero
char = LinΣ[ c ∈ ⟨ Alphabet ⟩ ] literal c

string-grammar : Grammar ℓ-zero
string-grammar = KL* char

⌈_⌉ : (w : String) → string-grammar w
⌈ [] ⌉ = nil _ refl
⌈ (x ∷ w) ⌉ =
  cons _ ((((x ∷ []) , w) , refl) , ((x , refl) , ⌈ w ⌉))
