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
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _ {ℓA}
  (A : Grammar ℓA)
  where
  Language : Type ℓA
  Language = Σ[ w ∈ String ] ∥ A w ∥₁

module _ {ℓA} {ℓB}
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  where

  record LogicalEquivalence : Type (ℓ-max ℓA ℓB) where
    no-eta-equality
    constructor mkLogEq
    field
      fun : A ⊢ B
      inv : B ⊢ A

  isLogicallyEquivalent : Type (ℓ-max ℓA ℓB)
  isLogicallyEquivalent = (A ⊢ B) × (B ⊢ A)

  open LogicalEquivalence
  LogicalEquivalence→isLogicallyEquivalent :
    LogicalEquivalence → isLogicallyEquivalent
  LogicalEquivalence→isLogicallyEquivalent LogEq .fst = LogEq .fun
  LogicalEquivalence→isLogicallyEquivalent LogEq .snd = LogEq .inv

  isWeaklyEquivalent : Type (ℓ-max ℓA ℓB)
  isWeaklyEquivalent = Iso (Language A) (Language B)

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

  isStronglyEquivalent : Type (ℓ-max ℓA ℓB)
  isStronglyEquivalent = ∀ w → Iso (A w) (B w)

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

  record StrongEquivalence : Type (ℓ-max ℓA ℓB) where
    no-eta-equality
    constructor mkStrEq
    field
      fun : A ⊢ B
      inv : B ⊢ A
      sec : fun ∘g inv ≡ id
      ret : inv ∘g fun ≡ id

  record isStrongEquivalence (e : A ⊢ B) : Type (ℓ-max ℓA ℓB) where
    no-eta-equality
    constructor isStrEq
    field
      inv : B ⊢ A
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

_≅_ : Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
A ≅ B = StrongEquivalence A B
infix 6 _≅_

_≈_ : Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
A ≈ B = LogicalEquivalence A B
infix 1 _≈_

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (pwIso : ∀ w → Iso (A w) (B w))
  where
  open StrongEquivalence
  open Iso

  pointwiseIso→≅ : A ≅ B
  pointwiseIso→≅ .fun w = pwIso w .fun
  pointwiseIso→≅ .inv w = pwIso w .inv
  pointwiseIso→≅ .sec = funExt λ w → funExt (pwIso w .rightInv)
  pointwiseIso→≅ .ret = funExt λ w → funExt (pwIso w .leftInv)

module _ {ℓA} {ℓB}
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (A≅B : A ≅ B)
  where

  open StrongEquivalence

  sym-strong-equivalence : B ≅ A
  sym-strong-equivalence .fun = A≅B .inv
  sym-strong-equivalence .inv = A≅B .fun
  sym-strong-equivalence .sec = A≅B .ret
  sym-strong-equivalence .ret = A≅B .sec

  sym≅ = sym-strong-equivalence

module _ {ℓA} {ℓB} {ℓC}
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  (A≅B : A ≅ B)
  (B≅C : B ≅ C)
  where

  open StrongEquivalence

  comp-strong-equiv : A ≅ C
  comp-strong-equiv .fun = B≅C .fun ∘g A≅B .fun
  comp-strong-equiv .inv = A≅B .inv ∘g B≅C .inv
  comp-strong-equiv .sec =
    (λ i → B≅C .fun ∘g A≅B .sec i ∘g B≅C .inv) ∙
    B≅C .sec
  comp-strong-equiv .ret =
    (λ i → A≅B .inv ∘g B≅C .ret i ∘g A≅B .fun) ∙
    A≅B .ret

_≅∙_ : A ≅ B → B ≅ C → A ≅ C
_≅∙_ = comp-strong-equiv
infixr 10 _≅∙_

module _ {ℓA} {ℓB}
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (A≈B : A ≈ B)
  where

  open LogicalEquivalence

  sym-log-equivalence : B ≈ A
  sym-log-equivalence .fun = A≈B .inv
  sym-log-equivalence .inv = A≈B .fun

  sym≈ = sym-log-equivalence

module _ {ℓA} {ℓB} {ℓC}
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  (A≈B : A ≈ B)
  (B≈C : B ≈ C)
  where

  open LogicalEquivalence

  comp-log-equiv : A ≈ C
  comp-log-equiv .fun = B≈C .fun ∘g A≈B .fun
  comp-log-equiv .inv = A≈B .inv ∘g B≈C .inv

_≈∙_ : A ≈ B → B ≈ C → A ≈ C
_≈∙_ = comp-log-equiv
infixr 10 _≈∙_

module _ {A : Grammar ℓA} where
  id≅ : A ≅ A
  id≅ = mkStrEq id id refl refl

hasRetraction→isMono :
  (e : A ⊢ B) →
  (inv : B ⊢ A) →
  (ret : inv ∘g e ≡ id) →
  isMono e
hasRetraction→isMono e inv ret f f' e∘f≡e∘f' =
  cong (_∘g f) (sym ret) ∙
  cong (inv ∘g_) e∘f≡e∘f' ∙
  cong (_∘g f') ret

open isStrongEquivalence
isStrongEquivalence→isMono :
  (e : A ⊢ B) →
  isStrongEquivalence _ _ e →
  isMono e
isStrongEquivalence→isMono e streq =
  hasRetraction→isMono e (streq .inv) (streq .ret)

