module Semantics.GrammarPowerCategory where

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

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper public
open import Semantics.String public
open import Semantics.Grammar public

private
  variable ℓ ℓ' ℓS : Level

module _ ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  -- TODO replace FinSet with Type
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)

  GRAMMAR : ∀ {ℓS} → Category (ℓ-max ℓ (ℓ-suc ℓS)) (ℓ-max ℓ ℓS)
  GRAMMAR {ℓS} = PowerCategory String (SET ℓS)

  open Functor

  ⊗F : Functor (GRAMMAR {ℓS} ×C GRAMMAR {ℓS}) (GRAMMAR {ℓ-max (ℓ-max ℓ ℓS) ℓS})
  fst (F-ob ⊗F (g , h) w) =
    Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × h (s .fst .snd) .fst
  snd (F-ob ⊗F (g , h) w) = {!!}
  F-hom ⊗F (g , h) w s = s .fst , (g _ (s .snd .fst) , h _ (s .snd .snd))
  F-id ⊗F = refl
  F-seq ⊗F _ _ = refl

  -- and so on with other connectives?
  -- how do you make parse trees?
