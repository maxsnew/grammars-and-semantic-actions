module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

LiftList : ∀ {L}{L'} → {A : Type L} → List A → List (Lift {L}{L'} A)
LiftList [] = []
LiftList (x ∷ xs) = lift x ∷ LiftList xs

LowerList : ∀ {L}{L'} → {A : Type L} → List (Lift {L}{L'} A) → List A
LowerList [] = []
LowerList (x ∷ xs) = lower x ∷ LowerList xs

LiftListDist : ∀ {L}{L'} {A : Type L} (w w' : List A) →
  LiftList {L}{L'} (w ++ w') ≡ (LiftList {L}{L'} w) ++ (LiftList {L}{L'} w')
LiftListDist [] w' = refl
LiftListDist (x ∷ w) w' = cong (lift x ∷_) (LiftListDist w w')
