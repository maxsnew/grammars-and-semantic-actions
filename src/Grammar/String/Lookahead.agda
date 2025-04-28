{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Lookahead (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.Maybe.Base hiding (rec)
open import Cubical.Data.Bool using (true ; false)

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet isSetAlphabet
import Grammar.Product.Binary.AsIndexed Alphabet isSetAlphabet as Ind&
open import Grammar.Sum Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet isSetAlphabet
open import Grammar.String.Base Alphabet isSetAlphabet
open import Grammar.String.Properties Alphabet isSetAlphabet
open import Grammar.Literal Alphabet isSetAlphabet
open import Grammar.Epsilon Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Grammar.LinearProduct Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Distributivity Alphabet isSetAlphabet

open import Term.Base Alphabet isSetAlphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

firstChar≅ : A ≅ (A & ε) ⊕ (⊕[ c ∈ Alphabet ] (A & startsWith c))
firstChar≅ =
  &string-split≅
  ≅∙ ⊕≅ id≅ (&≅ id≅ ⊕ᴰ-distLEq ≅∙ &⊕ᴰ-distR≅)

PeekChar : Maybe Alphabet → Grammar ℓ-zero
PeekChar nothing = ε
PeekChar (just c) = startsWith c

Peek : Grammar ℓA → Grammar ℓA
Peek A = ⊕[ c? ∈ Maybe Alphabet ] (A & PeekChar c?)

peek : A ≅ Peek A
peek =
  firstChar≅
  ≅∙ ⊕⊕ᴰ≅ _ _
  ≅∙ ⊕ᴰ≅ λ where
    nothing → sym≅ (LiftG≅ _ _)
    (just x) → sym≅ (LiftG≅ _ _)

@0 remember : ∀ {A : Grammar ℓ-zero} →
  (c? : Maybe Alphabet) →
  σ {X = Maybe Alphabet} {A = λ c'? → A & PeekChar c'?} c?
    ≡ peek .fun ∘g π₁
remember {A = A} c? =
  σ c?
    ≡⟨ cong (_∘g σ c?) (sym (peek .sec)) ⟩
  peek .fun ∘g peek .inv ∘g σ c?
    ≡⟨ cong (peek .fun ∘g_) (peek⁻∘σ≡π₁ c?) ⟩
  peek .fun ∘g π₁
  ∎
  where
  opaque
    unfolding π₁ ⊕-elim
    @0 peek⁻∘σ≡π₁ :
      ∀ (c? : Maybe Alphabet) →
      peek .inv
      ∘g σ {X = Maybe Alphabet} {A = λ c'? → A & PeekChar c'?} c?
        ≡ π₁
    peek⁻∘σ≡π₁ nothing = refl
    peek⁻∘σ≡π₁ (just c) = refl
