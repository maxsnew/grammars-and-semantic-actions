module Semantics.Grammar.Dependent where

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
open import Semantics.Grammar.Literal
open import Semantics.Grammar.KleeneStar

private
  variable ℓG ℓΣ₀ : Level

module _ {ℓG} {ℓS} {Σ₀ : Type ℓΣ₀} where
  open StringDefs {ℓΣ₀} {Σ₀}

  LinearΠ : {A : Type ℓS} → (A → Grammar ℓG {Σ₀}) → Grammar (ℓ-max ℓS ℓG)
  LinearΠ {A} f w = ∀ (a : A) → f a w

  LinearΣ : {A : Type ℓS} → (A → Grammar ℓG {Σ₀}) → Grammar (ℓ-max ℓS ℓG)
  LinearΣ {A} f w = Σ[ a ∈ A ] f a w

  LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG {Σ₀}) → Grammar (ℓ-max ℓS ℓG)
  LinearΣ-syntax = LinearΣ

  syntax LinearΣ-syntax {A} (λ x → B) = LinΣ[ x ∈ A ] B

module _ {ℓG} {Σ₀ : Type ℓΣ₀} where
  open StringDefs {ℓΣ₀} {Σ₀}
  ⊕Σ₀ : Grammar (ℓ-max ℓΣ₀ ℓG) {Σ₀}
  ⊕Σ₀ = LinearΣ λ (c : Σ₀) → literal {ℓG = ℓG} c

  String→KL* : (w : String) → KL* ⊕Σ₀ w
  String→KL* [] = nil (lift refl)
  String→KL* (x ∷ w) = cons ((([ x ] , w) , refl) , (((x , lift refl)) , (String→KL* w)))
