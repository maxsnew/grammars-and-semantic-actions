{-

Definition of finite sets

There are may different formulations of finite sets in constructive mathematics,
and we will use Bishop finiteness as is usually called in the literature.

-}
{-# OPTIONS --erased-cubical #-}

module Erased.Data.FinSet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as Prop

open import Erased.Data.Nat.Base
-- open import Erased.Data.Fin.Base renaming (Fin to Finℕ)
open import Erased.Data.SumFin.Base
import Erased.Data.Equality.Base as Eq
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

-- definition of (Bishop) finite sets

-- this definition makes cardinality computation more efficient
@0 isFinSet : Type ℓ → Type ℓ
isFinSet A = Σ ℕ λ n → ∥ A ≃ Fin n ∥₁

isFinOrd : Type ℓ → Type ℓ
isFinOrd A = Σ ℕ λ n → A ≃ Fin n

record IsoEq (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    fun : A → B
    inv : B → A
    rightInv : ∀ b → fun (inv b) Eq.≡ b
    leftInv : ∀ a → inv (fun a) Eq.≡ a

isFinOrd' : Type ℓ → Type ℓ
isFinOrd' A = Σ ℕ λ n → IsoEq A (Fin n)

@0 isFinOrd→isFinSet : isFinOrd A → isFinSet A
isFinOrd→isFinSet (_ , p) = _ , ∣ p ∣₁

-- finite sets are sets

@0 isFinSet→isSet : isFinSet A → isSet A
isFinSet→isSet p = rec isPropIsSet (λ e → isOfHLevelRespectEquiv 2 (invEquiv e) isSetFin) (p .snd)

-- isFinSet is proposition

-- isPropIsFinSet : isProp (isFinSet A)
-- isPropIsFinSet p q = Σ≡PropEquiv (λ _ → isPropPropTrunc) .fst (
--   Prop.elim2
--     (λ _ _ → isSetℕ _ _)
--     (λ p q → Fin-inj _ _ (ua (invEquiv (SumFin≃Fin _) ⋆ (invEquiv p) ⋆ q ⋆ SumFin≃Fin _)))
--     (p .snd) (q .snd))

-- -- isFinOrd is Set
-- -- ordering can be seen as extra structures over finite sets

-- isSetIsFinOrd : isSet (isFinOrd A)
-- isSetIsFinOrd = isOfHLevelΣ 2 isSetℕ (λ _ → isOfHLevel⁺≃ᵣ 1 isSetFin)

-- -- alternative definition of isFinSet

-- isFinSet' : Type ℓ → Type ℓ
-- isFinSet' A = ∥ Σ[ n ∈ ℕ ] A ≃ Fin n ∥₁

-- isFinSet→isFinSet' : isFinSet A → isFinSet' A
-- isFinSet→isFinSet' (_ , p) = Prop.rec isPropPropTrunc (λ p → ∣ _ , p ∣₁) p

-- isFinSet'→isFinSet : isFinSet' A → isFinSet A
-- isFinSet'→isFinSet = Prop.rec isPropIsFinSet (λ (n , p) → _ , ∣ p ∣₁ )

-- isFinSet≡isFinSet' : isFinSet A ≡ isFinSet' A
-- isFinSet≡isFinSet' = hPropExt isPropIsFinSet isPropPropTrunc isFinSet→isFinSet' isFinSet'→isFinSet

-- -- the type of finite sets/propositions

-- FinSet : (ℓ : Level) → Type (ℓ-suc ℓ)
-- FinSet ℓ = TypeWithStr _ isFinSet

-- FinProp : (ℓ : Level) → Type (ℓ-suc ℓ)
-- FinProp ℓ = Σ[ P ∈ FinSet ℓ ] isProp (P .fst)

-- -- cardinality of finite sets

-- card : FinSet ℓ → ℕ
-- card X = X .snd .fst

-- -- equality between finite sets/propositions

-- FinSet≡ : (X Y : FinSet ℓ) → (X .fst ≡ Y .fst) ≃ (X ≡ Y)
-- FinSet≡ _ _ = Σ≡PropEquiv (λ _ → isPropIsFinSet)

-- FinProp≡ : (X Y : FinProp ℓ) → (X .fst .fst ≡ Y .fst .fst) ≃ (X ≡ Y)
-- FinProp≡ X Y = compEquiv (FinSet≡ (X .fst) (Y .fst)) (Σ≡PropEquiv (λ _ → isPropIsProp))

-- -- hlevels of FinSet and FinProp

-- isGroupoidFinSet : isGroupoid (FinSet ℓ)
-- isGroupoidFinSet X Y =
--   isOfHLevelRespectEquiv 2 (FinSet≡ X Y)
--     (isOfHLevel≡ 2 (isFinSet→isSet (X .snd)) (isFinSet→isSet (Y .snd)))

-- isSetFinProp : isSet (FinProp ℓ)
-- isSetFinProp X Y =
--   isOfHLevelRespectEquiv 1 (FinProp≡ X Y) (isOfHLevel≡ 1 (X .snd) (Y .snd))
