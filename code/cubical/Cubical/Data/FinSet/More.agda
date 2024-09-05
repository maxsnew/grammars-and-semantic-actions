{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

isFinSet⊥ : isFinSet ⊥
isFinSet⊥ = isFinSetFin
