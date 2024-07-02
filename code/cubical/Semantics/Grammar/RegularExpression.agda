module Semantics.Grammar.RegularExpression where

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
open import Semantics.Grammar

private
  variable ℓG ℓG' ℓΣ₀ : Level


module _ {Σ₀ : Type ℓ-zero} where
  open StringDefs {ℓ-zero} {Σ₀}

  data RegularExpression  : Type ℓ-zero where
    ε-Reg : RegularExpression
    _⊗Reg_ : RegularExpression →
      RegularExpression → RegularExpression
    literalReg : Σ₀ → RegularExpression
    _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
    KL*Reg : RegularExpression → RegularExpression

  RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero {Σ₀}
  RegularExpression→Grammar  ε-Reg = ε-grammar
  RegularExpression→Grammar (g ⊗Reg g') =
    (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
  RegularExpression→Grammar (literalReg c) = literal c
  RegularExpression→Grammar (g ⊕Reg g') =
    RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
  RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

