open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Lookahead (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Maybe hiding (rec)
open import Cubical.Data.Bool using (true ; false)

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
import Grammar.Product.Binary.AsIndexed Alphabet as Ind&
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
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
PeekChar (just c) = startsWith c

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

remember : ∀ {A : Grammar ℓ-zero} →
  (c? : Maybe ⟨ Alphabet ⟩) →
  σ {X = Maybe ⟨ Alphabet ⟩} {A = λ c'? → A & PeekChar c'?} c?
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
    peek⁻∘σ≡π₁ :
      ∀ (c? : Maybe ⟨ Alphabet ⟩) →
      peek .inv
      ∘g σ {X = Maybe ⟨ Alphabet ⟩} {A = λ c'? → A & PeekChar c'?} c?
        ≡ π₁
    peek⁻∘σ≡π₁ nothing = refl
    peek⁻∘σ≡π₁ (just c) = refl

rememberInd : ∀ {A : Grammar ℓ-zero} →
  (c? : Maybe ⟨ Alphabet ⟩) →
  σ {X = Maybe ⟨ Alphabet ⟩} {A = λ c'? → A Ind&.& PeekChar c'?} c?
    ≡ peekInd .fun ∘g Ind&.π₁
rememberInd {A = A} c? =
  σ c?
    ≡⟨ cong (_∘g σ c?) (sym (peekInd .sec)) ⟩
  peekInd .fun ∘g peekInd .inv ∘g σ c?
    ≡⟨ cong (peekInd .fun ∘g_) (peek⁻∘σ≡π₁ c?) ⟩
  peekInd .fun ∘g Ind&.π₁ {A = Ind&.&Ind A (PeekChar c?)}
  ∎
  where
  opaque
    unfolding π₁ ⊕-elim
    peek⁻∘σ≡π₁ :
      ∀ (c? : Maybe ⟨ Alphabet ⟩) →
      peekInd .inv
      ∘g σ {X = Maybe ⟨ Alphabet ⟩} {A = λ c'? → A Ind&.& PeekChar c'?} c?
        ≡ Ind&.π₁
    peek⁻∘σ≡π₁ nothing = refl
    peek⁻∘σ≡π₁ (just c) = refl
