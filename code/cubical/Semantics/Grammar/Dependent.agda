open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Dependent ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.List

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Literal (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓS : Level

LinearΠ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ {A = A} f w = ∀ (a : A) → f a w

LinearΣ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ {A = A} f w = Σ[ a ∈ A ] f a w

LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ-syntax = LinearΣ

syntax LinearΣ-syntax {A} (λ x → B) = LinΣ[ x ∈ A ] B

⊕Σ₀ : Grammar ℓ-zero
⊕Σ₀ = LinearΣ λ (c : Σ₀) → literal c

String→KL* : (w : String) → KL* ⊕Σ₀ w
String→KL* [] = nil _ refl
String→KL* (x ∷ w) =
  cons _ ((([ x ] , w) , refl) , (((x , refl)) , (String→KL* w)))
