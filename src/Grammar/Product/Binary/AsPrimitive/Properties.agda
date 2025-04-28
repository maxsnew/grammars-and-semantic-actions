{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Binary.AsPrimitive.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Properties.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.Product Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
import Grammar.Product.Binary.AsIndexed.Base Alphabet isSetAlphabet as Ind&
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module _ {A : Grammar ℓA} {B : Grammar ℓB}
  (isSetA : isSetGrammar A) (isSetB : isSetGrammar B) where
  opaque
    unfolding _&_
    @0 isSetGrammar& : isSetGrammar (A & B)
    isSetGrammar& w = isSet× (isSetA w) (isSetB w)

@0 &unambiguous : unambiguous A → unambiguous B → unambiguous (A & B)
&unambiguous uA uB e e' = &≡ e e' (uA _ _) (uB _ _)

module _ (A B : Grammar ℓA) where
  Ind&→& : A Ind&.& B ⊢ A & B
  Ind&→& = Ind&.π₁ ,& Ind&.π₂

  &→Ind& : A & B ⊢ A Ind&.& B
  &→Ind& = π₁ Ind&.,& π₂

  private
    opaque
      unfolding _&_ &-intro π₁
      @0 the-sec : &→Ind& ∘g Ind&→& ≡ id
      the-sec = &ᴰ≡ _ _ λ where
        true → refl
        false → refl

      @0 the-ret : Ind&→& ∘g &→Ind& ≡ id
      the-ret = &≡ _ _ refl refl

  &≅Ind& : A & B ≅ A Ind&.& B
  &≅Ind& .fun = &→Ind&
  &≅Ind& .inv = Ind&→&
  &≅Ind& .sec = the-sec
  &≅Ind& .ret = the-ret
