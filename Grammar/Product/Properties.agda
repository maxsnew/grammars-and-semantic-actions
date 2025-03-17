open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module _
  {X : Type ℓX} {A : X → Grammar ℓA}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where
  opaque
    unfolding _⊗_

    &ᴰ-strengthL :
        (&[ x ∈ X ] B x) ⊗ A ⊢ &[ x ∈ X ] (B x ⊗ A)
    &ᴰ-strengthL w (s , f , pA) x = s , (f x , pA)

    &ᴰ-strengthR :
        A ⊗ (&[ x ∈ X ] B x) ⊢ &[ x ∈ X ] (A ⊗ B x)
    &ᴰ-strengthR w (s , pA , f) x = s , (pA , f x)
