module Semantics.Grammar.Literal where

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
open import Semantics.Grammar.Base

private
  variable ℓG ℓΣ₀ : Level

module _ {ℓG} {Σ₀ : Type ℓΣ₀} where
  open StringDefs {ℓΣ₀} {Σ₀}

  literal : Σ₀ → Grammar (ℓ-max ℓΣ₀ ℓG)
  literal c w = Lift {ℓΣ₀}{ℓ-max ℓΣ₀ ℓG} ( w ≡ [ c ] )
