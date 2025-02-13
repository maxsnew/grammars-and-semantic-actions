{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
import Cubical.Data.Nat.Order.Recursive as Ord
import Cubical.Data.Fin as Fin
open import Cubical.Data.SumFin
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

isFinSet⊥ : isFinSet ⊥
isFinSet⊥ = isFinSetFin

isFinSetLift :
  {L L' : Level} →
  {A : Type L} →
  isFinSet A → isFinSet (Lift {L}{L'} A)
fst (isFinSetLift {A = A} isFinSetA) = isFinSetA .fst
snd (isFinSetLift {A = A} isFinSetA) =
  PT.elim
  {P = λ _ → ∥ Lift A ≃ Fin (isFinSetA .fst) ∥₁}
  (λ [a] → isPropPropTrunc )
  (λ A≅Fin → ∣ compEquiv (invEquiv (LiftEquiv {A = A})) A≅Fin ∣₁)
  (isFinSetA .snd)

EquivPresIsFinOrd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → isFinOrd A → isFinOrd B
EquivPresIsFinOrd e (_ , p) = _ , compEquiv (invEquiv e) p

isFinOrdFin : ∀ {n} → isFinOrd (Fin n)
isFinOrdFin {n} = n , (idEquiv (Fin n))

isFinOrd⊥ : isFinOrd ⊥
fst isFinOrd⊥ = 0
snd isFinOrd⊥ = idEquiv ⊥

isFinOrdUnit : isFinOrd Unit
isFinOrdUnit =
  EquivPresIsFinOrd
    (isContr→Equiv isContrSumFin1 isContrUnit) isFinOrdFin

takeFirstFinOrd : ∀ {ℓ} → (A : Type ℓ) →
  (the-ord : isFinOrd A) → 0 Ord.< the-ord .fst → A
takeFirstFinOrd A (suc n , the-eq) x =
  the-eq .snd .equiv-proof (Fin→SumFin (Fin.fromℕ≤ 0 n x)) .fst .fst

isFinSet⊤ : isFinSet ⊤
isFinSet⊤ = 1 , ∣ invEquiv ⊎-IdR-⊥-≃ ∣₁
