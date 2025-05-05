{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lower ; lift ; liftExt ; liftFun)
open import Cubical.Foundations.HLevels

module Erased.Lift.Base where

private
  variable
    ℓ ℓ' : Level

record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
  constructor lift
  field
    lower : A

open Lift public

liftExt : ∀ {A : Type ℓ} {a b : Lift {ℓ} {ℓ'} A} → (lower a ≡ lower b) → a ≡ b
liftExt x i = lift (x i)

liftFun : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) → Lift {j = ℓ''} A → Lift {j = ℓ'''} B
liftFun f (lift a) = lift (f a)
