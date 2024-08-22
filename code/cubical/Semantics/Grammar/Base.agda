open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

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
open import Semantics.String (Σ₀ , isSetΣ₀) public

private
  variable ℓG ℓG' ℓH ℓK ℓL : Level

module _ where
  module _ ℓG where
    Grammar : Type (ℓ-suc ℓG)
    Grammar = String → Type ℓG

  module _ {ℓG}{ℓG'}
    (g : Grammar ℓG)
    where

    LiftGrammar : Grammar (ℓ-max ℓG ℓG')
    LiftGrammar w = Lift {ℓG}{ℓG'} (g w)

  -- module _ {ℓG}
  --   (g : Grammar ℓG)
  --   where
  --   Language : Type ℓG
  --   Language = Σ[ w ∈ String ] ∥ g w ∥₁

  -- module _ {ℓG} {ℓG'}
  --   (g : Grammar ℓG)
  --   (g' : Grammar ℓG')
  --   where

  --   isLogicallyEquivalent : Type (ℓ-max ℓG ℓG')
  --   isLogicallyEquivalent = (g ⊢ g') × (g' ⊢ g)

  --   isWeaklyEquivalent : Type (ℓ-max ℓG ℓG')
  --   isWeaklyEquivalent = Iso (Language g) (Language g')

  --   open Iso
  --   isLogicalEquivalence→WeakEquivalence :
  --     isLogicallyEquivalent → isWeaklyEquivalent
  --   fst (fun (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
  --   snd (fun (isLogicalEquivalence→WeakEquivalence logEq) x) =
  --     PT.rec
  --       isPropPropTrunc
  --       (λ p → ∣ logEq .fst p ∣₁)
  --       (x .snd)
  --   fst (inv (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
  --   snd (inv (isLogicalEquivalence→WeakEquivalence logEq) x) =
  --     PT.rec
  --       isPropPropTrunc
  --       (λ p → ∣ logEq .snd p ∣₁)
  --       (x .snd)
  --   rightInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
  --     Σ≡Prop (λ _ → isPropPropTrunc) refl
  --   leftInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
  --     Σ≡Prop (λ _ → isPropPropTrunc) refl

  --   isStronglyEquivalent : Type (ℓ-max ℓG ℓG')
  --   isStronglyEquivalent = ∀ w → Iso (g w) (g' w)

  --   isStronglyEquivalent→isWeaklyEquivalent :
  --     isStronglyEquivalent → isWeaklyEquivalent
  --   fst (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
  --   snd (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
  --     PT.rec
  --       isPropPropTrunc
  --       (λ p → ∣ strEq (x .fst) .fun p ∣₁)
  --       (x .snd)
  --   fst (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
  --   snd (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
  --     PT.rec
  --       isPropPropTrunc
  --       (λ p → ∣ strEq (x .fst) .inv p ∣₁)
  --       (x .snd)
  --   rightInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
  --     Σ≡Prop (λ _ → isPropPropTrunc) refl
  --   leftInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
  --     Σ≡Prop (λ _ → isPropPropTrunc) refl
