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

module _ {(Σ₀ , isFinSetΣ₀) : FinSet ℓΣ₀} where
  open GrammarDefs (Σ₀ , isFinSetΣ₀)

  literal : Σ₀ → Grammar ℓΣ₀
  literal c w = w ≡ [ c ]

  isHGrammar-literal : ∀ c → isHGrammar ℓΣ₀ (literal c)
  isHGrammar-literal c w = isGroupoidString _ _
