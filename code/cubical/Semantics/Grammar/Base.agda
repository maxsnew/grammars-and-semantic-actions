module Semantics.Grammar.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper
open import Semantics.String

private
  variable ℓG ℓG' ℓΣ₀ : Level

module _ ℓG {Σ₀ : Type ℓΣ₀} where
  open StringDefs {ℓΣ₀} {Σ₀}
  Grammar : Type (ℓ-max ℓΣ₀ (ℓ-suc ℓG))
  Grammar = String → Type ℓG

module _ {ℓG} {ℓG'} {Σ₀ : Type ℓΣ₀} where
  Term : Grammar ℓG {Σ₀} → Grammar ℓG' → Type (ℓ-max (ℓ-max ℓG ℓG') ℓΣ₀)
  Term g g' = ∀ {w} → g w → g' w

  infix 5 Term
  syntax Term g g' = g ⊢ g'
