open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.DecPropGrammar ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

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
open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Top (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Bottom (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓS : Level

DecProp-grammar' :
  DecProp ℓS → Grammar (ℓ-max ℓS ℓG)
DecProp-grammar' d =
  decRec
    (λ _ → ⊤-grammar)
    (λ _ → ⊥-grammar) (d .snd)
