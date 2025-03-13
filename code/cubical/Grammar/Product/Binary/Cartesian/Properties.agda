open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Binary.Cartesian.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Grammar.Base Alphabet
open import Grammar.Properties.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.Cartesian.Base Alphabet
import Grammar.Product.Binary.Inductive.Base Alphabet as Ind&
open import Term.Base Alphabet

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
    isSetGrammar& : isSetGrammar (A & B)
    isSetGrammar& w = isSet× (isSetA w) (isSetB w)

-- TODO : derive from a general product unambiguity
&unambiguous : unambiguous A → unambiguous B →
  unambiguous (A & B)
&unambiguous uA uB e e' = &≡ e e' (uA _ _) (uB _ _)

module _ (A B : Grammar ℓA) where
  Ind&→& : A Ind&.& B ⊢ A & B
  Ind&→& = Ind&.π₁ ,& Ind&.π₂

  &→Ind& : A & B ⊢ A Ind&.& B
  &→Ind& = π₁ Ind&.,& π₂

  private
    opaque
      unfolding _&_ &-intro π₁
      the-sec : &→Ind& ∘g Ind&→& ≡ id
      the-sec = &ᴰ≡ _ _ λ where
        true → refl
        false → refl

      the-ret : Ind&→& ∘g &→Ind& ≡ id
      the-ret = &≡ _ _ refl refl

  &≅Ind& : A & B ≅ A Ind&.& B
  &≅Ind& .fun = &→Ind&
  &≅Ind& .inv = Ind&→&
  &≅Ind& .sec = the-sec
  &≅Ind& .ret = the-ret
