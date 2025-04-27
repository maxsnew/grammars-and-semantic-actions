{-# OPTIONS --erased-cubical #-}
module Erased.Data.List.Properties where

open import Erased.Data.List.Base
import Erased.Data.Equality.Base as Eq

open import Cubical.Foundations.Prelude

open import Cubical.Data.Maybe.Base as Maybe hiding (rec ; elim)
open import Cubical.Data.Nat.Base hiding (elim)

module _ {ℓ : Level} {A : Type ℓ} where
  ++-unit-r-Eq : (xs : List A) → xs ++ [] Eq.≡ xs
  ++-unit-r-Eq [] = Eq.refl
  ++-unit-r-Eq (x ∷ xs) = Eq.ap (_∷_ x) (++-unit-r-Eq xs)

  ++-assoc-Eq : (xs ys zs : List A) → (xs ++ ys) ++ zs Eq.≡ xs ++ ys ++ zs
  ++-assoc-Eq [] ys zs = Eq.refl
  ++-assoc-Eq (x ∷ xs) ys zs = Eq.ap (_∷_ x) (++-assoc-Eq xs ys zs)

  @0 ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-r [] = refl
  ++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

  @0 ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)
