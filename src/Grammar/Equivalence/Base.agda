open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

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

module _ {ℓA} {ℓB}
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  where

  record WeakEquivalence : Type (ℓ-max ℓA ℓB) where
    no-eta-equality
    constructor mkLogEq
    field
      fun : A ⊢ B
      inv : B ⊢ A

  isWeaklyEquivalent : Type (ℓ-max ℓA ℓB)
  isWeaklyEquivalent = (A ⊢ B) × (B ⊢ A)

  open WeakEquivalence
  WeakEquivalence→isWeaklyEquivalent :
    WeakEquivalence → isWeaklyEquivalent
  WeakEquivalence→isWeaklyEquivalent LogEq .fst = LogEq .fun
  WeakEquivalence→isWeaklyEquivalent LogEq .snd = LogEq .inv

  open Iso

  isStronglyEquivalent : Type (ℓ-max ℓA ℓB)
  isStronglyEquivalent = ∀ w → Iso (A w) (B w)

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

  StrongEquivalence→isStrongEquivalence : (eq : StrongEquivalence) → isStrongEquivalence (eq .StrongEquivalence.fun)
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
A ≈ B = WeakEquivalence A B
infix 1 _≈_

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

  open WeakEquivalence

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

  open WeakEquivalence

  comp-weak-equiv : A ≈ C
  comp-weak-equiv .fun = B≈C .fun ∘g A≈B .fun
  comp-weak-equiv .inv = A≈B .inv ∘g B≈C .inv

_≈∙_ : A ≈ B → B ≈ C → A ≈ C
_≈∙_ = comp-weak-equiv
infixr 10 _≈∙_

module _ {A : Grammar ℓA} where
  id≅ : A ≅ A
  id≅ = mkStrEq id id refl refl

open WeakEquivalence
record _isRetractOf_ (A : Grammar ℓA) (B : Grammar ℓB) : Type (ℓ-max ℓA ℓB) where
  field
    weak : A ≈ B
    ret : weak .inv ∘g weak .fun ≡ id

infixr 10 _isRetractOf_

hasRetraction→isMono :
  (e : A ⊢ B) →
  (inv : B ⊢ A) →
  (ret : inv ∘g e ≡ id) →
  isMono e
hasRetraction→isMono e inv ret f f' e∘f≡e∘f' =
  cong (_∘g f) (sym ret) ∙
  cong (inv ∘g_) e∘f≡e∘f' ∙
  cong (_∘g f') ret

open _isRetractOf_
isRetractOf→isMono : (isRet : A isRetractOf B) → isMono (isRet .weak .fun)
isRetractOf→isMono isRet =
  hasRetraction→isMono (isRet .weak .fun) (isRet .weak .inv) (isRet .ret)

open isStrongEquivalence
isStrongEquivalence→isMono :
  (e : A ⊢ B) →
  isStrongEquivalence _ _ e →
  isMono e
isStrongEquivalence→isMono e streq =
  hasRetraction→isMono e (streq .inv) (streq .ret)

