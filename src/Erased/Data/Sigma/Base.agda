{- Basic definitions using Σ-types

Σ-types are defined in Core/Primitives as they are needed for Glue types.

The file contains:

- Non-dependent pair types: A × B
- Mere existence: ∃[x ∈ A] B
- Unique existence: ∃![x ∈ A] B

-}
module Erased.Data.Sigma.Base where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base


-- Non-dependent pair types

_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infixr 5 _×_


-- Mere existence

@0 ∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ∥ Σ A B ∥₁

infix 2 ∃-syntax

@0 ∃-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B


-- Unique existence

@0 ∃! : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃! A B = isContr (Σ A B)

infix 2 ∃!-syntax

@0 ∃!-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃!-syntax = ∃!

syntax ∃!-syntax A (λ x → B) = ∃![ x ∈ A ] B
