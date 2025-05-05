{-# OPTIONS --cubical #-}
module Cubical.Data.Sum.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding

open import Cubical.Data.Sum.Base as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open Iso

private
  variable
    ℓa ℓb ℓc ℓd ℓe : Level
    A : Type ℓa
    B : A → Type ℓb
    C : A → Type ℓc

module _
  (A : Type ℓa)
  (B : A → Type ℓb)
  (C : A → Type ℓc)
  where
  ΣDistR⊎Iso :
    Iso
      (Σ[ a ∈ A ] (B a ⊎ C a))
      ((Σ[ a ∈ A ] B a) ⊎ (Σ[ a ∈ A ] C a))
  ΣDistR⊎Iso .fun (a , inl b) = inl (a , b)
  ΣDistR⊎Iso .fun (a , inr c) = inr (a , c)
  ΣDistR⊎Iso .inv (inl (a , b)) = a , (inl b)
  ΣDistR⊎Iso .inv (inr (a , c)) = a , (inr c)
  ΣDistR⊎Iso .rightInv (inl (a , b)) = refl
  ΣDistR⊎Iso .rightInv (inr (a , c)) = refl
  ΣDistR⊎Iso .leftInv (a , inl b) = refl
  ΣDistR⊎Iso .leftInv (a , inr c) = refl
