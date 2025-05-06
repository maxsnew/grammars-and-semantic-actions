{-# OPTIONS --erased-cubical #-}
module Cubical.Data.Sigma.ErasedSnd where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

record Σ0 (X : Type ℓ) (Y : X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor _,_
  field
    fst0 : X
    @0 snd0 : Y fst0

infix 2 Σ0-syntax

Σ0-syntax : (X : Type ℓ) (Y : X → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ0-syntax = Σ0

syntax Σ0-syntax X (λ x → Y) = Σ0[ x ∈ X ] Y

open Σ0 public
