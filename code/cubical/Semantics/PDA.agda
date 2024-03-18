{-# OPTIONS #-}
module Semantics.PDA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty.Base
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.Instances.FreeComMonoid

open import Cubical.Tactics.Reflection
open import Semantics.Grammar

private
  variable ℓ ℓ' : Level

module PDA ℓ (Σ₀ : hSet ℓ) (Γ₀ : hSet ℓ) where
  open GrammarDefs ℓ Σ₀

  record PDA : Type ? where
    constructor mkPDA
    field
      Q : FinSet ℓ
      init : Q .fst
      acc : Q .fst
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀ .fst
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst
