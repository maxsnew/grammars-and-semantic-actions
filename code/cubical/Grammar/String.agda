open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Literal Alphabet
open import Grammar.KleeneStar Alphabet

char : Grammar ℓ-zero
char = LinΣ[ c ∈ ⟨ Alphabet ⟩ ] literal c

string-grammar : Grammar ℓ-zero
string-grammar = KL* char

⌈_⌉ : (w : String) → string-grammar w
⌈ [] ⌉ = nil _ refl
⌈ (x ∷ w) ⌉ =
  cons _ ((((x ∷ []) , w) , refl) , ((x , refl) , ⌈ w ⌉))
