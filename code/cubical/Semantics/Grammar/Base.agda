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
  variable ℓG ℓG' ℓΣ₀ : Level

module GrammarDefs ((Σ₀ , isFinSetΣ₀) : FinSet ℓ-zero) where
  open StringDefs (Σ₀ , isFinSetΣ₀) public

  module _ ℓG where
    Grammar : Type (ℓ-suc ℓG)
    Grammar = String → Type ℓG

    isHGrammar : Grammar → Type ℓG
    isHGrammar g = ∀ w → isSet (g w)

    hGrammar : Type (ℓ-suc ℓG)
    hGrammar = Σ[ g ∈ Grammar ] isHGrammar g


  module _ {ℓG} where
    Term : Grammar ℓG → Grammar ℓG → Type ℓG
    Term g g' = ∀ {w} → g w → g' w

    infix 5 Term
    syntax Term g g' = g ⊢ g'

    ε-grammar : Grammar ℓG
    ε-grammar w = LiftList {ℓ-zero}{ℓG} w ≡ []

  -- isHGrammar-ε-grammar : isHGrammar ℓΣ₀ ε-grammar
  -- isHGrammar-ε-grammar w = isGroupoidString w []

  -- literal : Σ₀ → Grammar ℓΣ₀
  -- literal c w = w ≡ [ c ]

  -- isHGrammar-literal : ∀ c → isHGrammar ℓΣ₀ (literal c)
  -- isHGrammar-literal c w = isGroupoidString _ _
