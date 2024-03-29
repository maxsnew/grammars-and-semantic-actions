module Semantics.String where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Semantics.Helper public

private
  variable ℓ ℓ' : Level

module StringDefs ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w =
    isSetΣ (isSet× isSetString isSetString)
      λ s → isGroupoidString w (s .fst ++ s .snd)

  module _ (c : Σ₀ .fst) where
    splitChar : (w : String) → Splitting (c ∷ w)
    splitChar w = ([ c ] , w) , refl
