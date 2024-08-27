open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Equivalence ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
-- open import Semantics.Term.Rules (Σ₀ , isSetΣ₀)
module _ {ℓG}
  (g : Grammar ℓG)
  where
  Language : Type ℓG
  Language = Σ[ w ∈ String ] ∥ g w ∥₁

module _ {ℓG} {ℓG'}
  (g : Grammar ℓG)
  (g' : Grammar ℓG')
  where

  isLogicallyEquivalent : Type (ℓ-max ℓG ℓG')
  isLogicallyEquivalent = (g ⊢ g') × (g' ⊢ g)

  isWeaklyEquivalent : Type (ℓ-max ℓG ℓG')
  isWeaklyEquivalent = Iso (Language g) (Language g')

  open Iso
  isLogicalEquivalence→WeakEquivalence :
    isLogicallyEquivalent → isWeaklyEquivalent
  fst (fun (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
  snd (fun (isLogicalEquivalence→WeakEquivalence logEq) x) =
    rec isPropPropTrunc (λ p → ∣ logEq .fst _ p ∣₁) (x .snd)
  fst (inv (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
  snd (inv (isLogicalEquivalence→WeakEquivalence logEq) x) =
    rec isPropPropTrunc (λ p → ∣ logEq .snd _ p ∣₁) (x .snd)
  rightInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
    Σ≡Prop (λ _ → isPropPropTrunc) refl
  leftInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
    Σ≡Prop (λ _ → isPropPropTrunc) refl

  isStronglyEquivalent : Type (ℓ-max ℓG ℓG')
  isStronglyEquivalent = ∀ w → Iso (g w) (g' w)

  isStronglyEquivalent→isWeaklyEquivalent :
    isStronglyEquivalent → isWeaklyEquivalent
  fst (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
  snd (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
    PT.rec
      isPropPropTrunc
      (λ p → ∣ strEq (x .fst) .fun p ∣₁)
      (x .snd)
  fst (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
  snd (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
    PT.rec
      isPropPropTrunc
      (λ p → ∣ strEq (x .fst) .inv p ∣₁)
      (x .snd)
  rightInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
    Σ≡Prop (λ _ → isPropPropTrunc) refl
  leftInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
    Σ≡Prop (λ _ → isPropPropTrunc) refl

  record StrongEquivalence : Type (ℓ-max ℓG ℓG') where
    no-eta-equality
    constructor mkStrEq
    field
      fun : g ⊢ g'
      inv : g' ⊢ g
      sec : fun ∘g inv ≡ id
      ret : inv ∘g fun ≡ id
