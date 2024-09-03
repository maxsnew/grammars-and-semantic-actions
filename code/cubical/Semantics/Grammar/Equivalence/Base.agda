open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Equivalence.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)

module _ {ℓG}
  (g : Grammar ℓG)
  where
  Language : Type ℓG
  Language = Σ[ w ∈ String ] ∥ g w ∥₁

module _ {ℓG} {ℓG'}
  (g : Grammar ℓG)
  (g' : Grammar ℓG')
  where

  record LogicalEquivalence : Type (ℓ-max ℓG ℓG') where
    no-eta-equality
    constructor mkLogEq
    field
      fun : g ⊢ g'
      inv : g' ⊢ g

  isLogicallyEquivalent : Type (ℓ-max ℓG ℓG')
  isLogicallyEquivalent = (g ⊢ g') × (g' ⊢ g)

  open LogicalEquivalence
  LogicalEquivalence→isLogicallyEquivalent :
    LogicalEquivalence → isLogicallyEquivalent
  LogicalEquivalence→isLogicallyEquivalent LogEq .fst = LogEq .fun
  LogicalEquivalence→isLogicallyEquivalent LogEq .snd = LogEq .inv

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

module _ {ℓG} {ℓH}
  {g : Grammar ℓG}
  {h : Grammar ℓH}
  (g≅h : StrongEquivalence g h)
  where

  open StrongEquivalence

  sym-strong-equivalence : StrongEquivalence h g
  sym-strong-equivalence .fun = g≅h .inv
  sym-strong-equivalence .inv = g≅h .fun
  sym-strong-equivalence .sec = g≅h .ret
  sym-strong-equivalence .ret = g≅h .sec

module _ {ℓG} {ℓH} {ℓK}
  {g : Grammar ℓG}
  {h : Grammar ℓH}
  {k : Grammar ℓK}
  (g≅h : StrongEquivalence g h)
  (h≅k : StrongEquivalence h k)
  where

  open StrongEquivalence

  comp-strong-equiv : StrongEquivalence g k
  comp-strong-equiv .fun = h≅k .fun ∘g g≅h .fun
  comp-strong-equiv .inv = g≅h .inv ∘g h≅k .inv
  comp-strong-equiv .sec =
    (λ i → h≅k .fun ∘g g≅h .sec i ∘g h≅k .inv) ∙
    h≅k .sec
  comp-strong-equiv .ret =
    (λ i → g≅h .inv ∘g h≅k .ret i ∘g g≅h .fun) ∙
    g≅h .ret
