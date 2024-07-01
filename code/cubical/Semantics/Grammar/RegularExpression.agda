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


module _ {Σ₀ : Type ℓΣ₀} where
  open StringDefs {ℓΣ₀} {Σ₀}

  data RegularExpression  : (L : Level) → Typeω where
    ε-Reg : ∀ {L} → RegularExpression (ℓ-max L ℓΣ₀)
    _⊗Reg_ : ∀ {L} {L'} → RegularExpression L →
      RegularExpression L' → RegularExpression (ℓ-max L (ℓ-max ℓΣ₀ L'))
    literalReg : ∀ {L} → Σ₀ → RegularExpression (ℓ-max L ℓΣ₀)
    _⊕Reg_ : ∀ {L} {L'} → RegularExpression L → RegularExpression L' → RegularExpression (ℓ-max L L')
    KL*Reg : ∀ {L} → RegularExpression L → RegularExpression (ℓ-max ℓΣ₀ (ℓ-suc L))

  RegularExpression→Grammar : ∀ {L} → RegularExpression L → Grammar L {Σ₀}
  RegularExpression→Grammar {L} ε-Reg = ε-grammar {ℓG = L}
  RegularExpression→Grammar (g ⊗Reg g') =
    (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
  RegularExpression→Grammar {L} (literalReg c) = literal {ℓG = L} c
  RegularExpression→Grammar (g ⊕Reg g') =
    RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
  RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

