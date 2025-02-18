{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Data.Maybe.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels.MoreMore

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.More
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓA ℓB ℓC : Level
    A : Type ℓA
    B : Type ℓB
    C : Type ℓC

nothingDiscrete : (x : Maybe A) → Dec (x ≡ nothing)
nothingDiscrete nothing = yes refl
nothingDiscrete (just x) = no ¬just≡nothing

nothingOrJust : (x : Maybe A) → (x ≡ nothing) ⊎ (Σ[ a ∈ A ] x ≡ just a)
nothingOrJust nothing = inl refl
nothingOrJust (just a) = inr (a , refl)

module _
  {A : Type ℓA}
  {B : Type ℓB}
  {f : A → B}
  where
  map-Maybe-fiber : (x : Maybe A) → fiber just (map-Maybe f x) → fiber just x
  map-Maybe-fiber nothing (b , b≡) = Empty.rec (¬just≡nothing b≡)
  map-Maybe-fiber (just a) (b , b≡) = a , refl
