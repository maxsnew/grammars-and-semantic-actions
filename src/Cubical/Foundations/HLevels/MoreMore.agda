{-# OPTIONS --cubical #-}
module Cubical.Foundations.HLevels.MoreMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable ℓ ℓ' : Level

isPropLift :
  {L L' : Level} →
  {A : Type L} →
  isProp A → isProp (Lift {L}{L'} A)
isPropLift x a b = liftExt (x _ _)

isSetLift :
  {L L' : Level} →
  {A : Type L} →
  isSet A → isSet (Lift {L}{L'} A)
isSetLift isSetA x y a b i =
  liftExt
    (isSetA (lower x) (lower y)
    (cong lower a) (cong lower b) i)

isGroupoidLift :
  {L L' : Level} →
  {A : Type L} →
  isGroupoid A → isGroupoid (Lift {L}{L'} A)
isGroupoidLift isGroupoidA x y a b u v i j k =
  lift
  ((isGroupoidA (lower x) (lower y)) (cong lower a)
    (cong lower b) (cong (cong lower) u) (cong (cong lower) v) i j k)

isPropCod→isProp≃ :
  {a : Type ℓ}{b : Type ℓ'} →
  isProp b → isProp (a ≃ b)
isPropCod→isProp≃ isPropB =
  isPropΣ
     (isProp→ isPropB)
    λ f → isPropIsEquiv f
