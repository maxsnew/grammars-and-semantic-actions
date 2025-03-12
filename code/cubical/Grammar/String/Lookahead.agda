open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Lookahead (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Maybe hiding (rec)

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.Cartesian Alphabet
import Grammar.Product.Binary.Inductive Alphabet as Ind&
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.Cartesian Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Lift Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Distributivity Alphabet

open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

firstChar≅ : A ≅ (A & ε) ⊕ (⊕[ c ∈ ⟨ Alphabet ⟩ ] (A & startsWith c))
firstChar≅ =
  &string-split≅
  ≅∙ ⊕≅ id≅ (&≅ id≅ ⊕ᴰ-distL ≅∙ &⊕ᴰ-distR≅)

PeekChar : Maybe ⟨ Alphabet ⟩ → Grammar ℓ-zero
PeekChar nothing = ε
PeekChar (just c) = ＂ c ＂ ⊗ string

Peek : Grammar ℓA → Grammar ℓA
Peek A = ⊕[ c? ∈ Maybe ⟨ Alphabet ⟩ ] (A & PeekChar c?)

PeekInd : Grammar ℓ-zero → Grammar ℓ-zero
PeekInd A = ⊕[ c? ∈ Maybe ⟨ Alphabet ⟩ ] (A Ind&.& PeekChar c?)

peek : A ≅ Peek A
peek =
  firstChar≅
  ≅∙ ⊕⊕ᴰ≅ _ _
  ≅∙ ⊕ᴰ≅ λ where
    nothing → sym≅ (LiftG≅ _ _)
    (just x) → sym≅ (LiftG≅ _ _)

peekInd : A ≅ PeekInd A
peekInd =
  peek
  ≅∙ ⊕ᴰ≅ λ where
    nothing → &≅Ind& _ _
    (just x) → &≅Ind& _ _
