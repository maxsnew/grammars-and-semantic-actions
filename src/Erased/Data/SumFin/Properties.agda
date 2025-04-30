{-# OPTIONS --erased-cubical #-}
module Erased.Data.SumFin.Properties where

open import Cubical.Foundations.Prelude

open import Erased.Data.Empty as ⊥ using (⊥)
open import Erased.Data.Unit using (tt) renaming (Unit to ⊤) public
open import Erased.Data.Sum.Base using (_⊎_; inl; inr) public

open import Erased.Data.Nat.Base hiding (elim)
open import Erased.Data.Nat.Properties
open import Erased.Data.SumFin.Base
import Erased.Data.Equality as Eq

open import Erased.Relation.Nullary.Base
open import Erased.Relation.Nullary.Properties

private
  variable
    ℓ : Level
    k : ℕ

decEqFin : ∀ n → DecEq (Fin n)
decEqFin (suc n) fzero fzero = yes Eq.refl
decEqFin (suc n) fzero (fsuc y) = no (λ ())
decEqFin (suc n) (fsuc x) fzero = no (λ ())
decEqFin (suc n) (fsuc x) (fsuc y) with decEqFin n x y
... | yes Eq.refl = yes Eq.refl
... | no p = no (λ where Eq.refl → p Eq.refl)
