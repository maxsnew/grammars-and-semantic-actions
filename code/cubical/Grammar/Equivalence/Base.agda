open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

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

  record isStrongEquivalence (e : g ⊢ g') : Type (ℓ-max ℓG ℓG') where
    no-eta-equality
    constructor isStrEq
    field
      inv : g' ⊢ g
      sec : e ∘g inv ≡ id
      ret : inv ∘g e ≡ id

  StrongEquivalence→isStrongEquivalence :
    (eq : StrongEquivalence) →
      isStrongEquivalence (eq .StrongEquivalence.fun)
  StrongEquivalence→isStrongEquivalence eq
    .isStrongEquivalence.inv = eq .StrongEquivalence.inv
  StrongEquivalence→isStrongEquivalence eq
    .isStrongEquivalence.sec = eq .StrongEquivalence.sec
  StrongEquivalence→isStrongEquivalence eq
    .isStrongEquivalence.ret = eq .StrongEquivalence.ret

_≅_ : Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
g ≅ g' = StrongEquivalence g g'
infix 5 _≅_

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

  sym≅ = sym-strong-equivalence

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

_≅∙_ : g ≅ h → h ≅ k → g ≅ k
_≅∙_ = comp-strong-equiv
infixr 10 _≅∙_

hasRetraction→isMono :
  (e : g ⊢ h) →
  (inv : h ⊢ g) →
  (ret : inv ∘g e ≡ id) →
  isMono e
hasRetraction→isMono e inv ret f f' e∘f≡e∘f' =
  cong (_∘g f) (sym ret) ∙
  cong (inv ∘g_) e∘f≡e∘f' ∙
  cong (_∘g f') ret

open isStrongEquivalence
isStrongEquivalence→isMono :
  (e : g ⊢ h) →
  isStrongEquivalence _ _ e →
  isMono e
isStrongEquivalence→isMono e streq =
  hasRetraction→isMono e (streq .inv) (streq .ret)

