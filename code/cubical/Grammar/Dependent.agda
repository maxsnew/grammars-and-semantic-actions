open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Literal Alphabet


private
  variable
    ℓG ℓS : Level

LinearΠ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ {A = A} f w = ∀ (a : A) → f a w

LinearΣ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ {A = A} f w = Σ[ a ∈ A ] f a w

LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ-syntax = LinearΣ

syntax LinearΣ-syntax {A = A} (λ x → B) = LinΣ[ x ∈ A ] B

⊕Σ₀ : Grammar ℓ-zero
⊕Σ₀ = LinearΣ λ (c : ⟨ Alphabet ⟩ ) → literal c
