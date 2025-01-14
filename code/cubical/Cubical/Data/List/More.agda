module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Empty

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

module _ {ℓ : Level} {A : Type ℓ} where
  different-lengths :
    {xs ys : List A} →
    ((length xs) ≡ (length ys) → ⊥) →
    xs ≡ ys → ⊥
  different-lengths {xs = []} {ys = []} f _ = f refl
  different-lengths {xs = []} {ys = y ∷ ys} f = ¬nil≡cons
  different-lengths {xs = x ∷ xs} {ys = []} f = ¬cons≡nil
  different-lengths {xs = x ∷ xs} {ys = y ∷ ys} f cons≡ =
    different-lengths (λ len≡ → f (cong suc len≡)) (cons-inj₂ cons≡)
