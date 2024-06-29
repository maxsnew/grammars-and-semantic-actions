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

open import Semantics.Helper public
open import Semantics.String public

private
  variable ℓG ℓΣ₀ : Level

module GrammarDefs ((Σ₀ , isFinSetΣ₀) : FinSet ℓΣ₀) where
  open StringDefs (Σ₀ , isFinSetΣ₀) public

  module _ ℓG where
    private
      ℓ : Level
      ℓ = ℓ-max ℓG ℓΣ₀

    Grammar : Type (ℓ-suc ℓ)
    Grammar = String → Type ℓ

    isHGrammar : Grammar → Type ℓ
    isHGrammar g = ∀ w → isSet (g w)

    hGrammar : Type (ℓ-suc ℓ)
    hGrammar = Σ[ g ∈ Grammar ] isHGrammar g
