open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Sum.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.SumFin
import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

_⊕'_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A ⊕' B) w = A w ⊎ B w
infixr 18 _⊕'_
opaque
  _⊕_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  _⊕_ = _⊕'_

infixr 18 _⊕_

opaque
  unfolding _⊕_
  ⊕-inl :
    A ⊢ A ⊕ B
  ⊕-inl _ p = inl p


  ⊕-inr :
    A ⊢ B ⊕ A
  ⊕-inr _ p = inr p

  ⊕-elim :
    A ⊢ B →
    C ⊢ B →
    A ⊕ C ⊢ B
  ⊕-elim eA eB _ p =
    Sum.elim
      (λ pA → eA _ pA)
      (λ pB → eB _ pB)
      p

  ⊕≡ :
    (f f' : A ⊕ C ⊢ B)
    → (f ∘g ⊕-inl ≡ f' ∘g ⊕-inl)
    → (f ∘g ⊕-inr ≡ f' ∘g ⊕-inr)
    → f ≡ f'
  ⊕≡ f f' f≡f'inl f≡f'inr = funExt λ w → funExt λ
    { (inl x) → funExt⁻ (funExt⁻ f≡f'inl _) x
    ; (inr x) → funExt⁻ (funExt⁻ f≡f'inr _) x }

  ⊕-βl :
    (e₁ : A ⊢ C) →
    (e₂ : B ⊢ C) →
    ⊕-inl ⋆ ⊕-elim e₁ e₂
      ≡
    e₁
  ⊕-βl e₁ e₂ = refl

  ⊕-βr :
    (e₁ : A ⊢ C) →
    (e₂ : B ⊢ C) →
    ⊕-inr ⋆ ⊕-elim e₁ e₂
      ≡
    e₂
  ⊕-βr e₁ e₂ = refl

  ⊕-η :
    (e : A ⊕ B ⊢ C) →
    (⊕-elim {A = A}{B = C}{C = B}
      (e ∘g ⊕-inl)
      (e ∘g ⊕-inr)
    )
      ≡
      e
  ⊕-η e i _ (inl x) = e _ (inl x)
  ⊕-η e i _ (inr x) = e _ (inr x)

_,⊕p_ :
  A ⊢ B →
  C ⊢ D →
  A ⊕ C ⊢ B ⊕ D
e ,⊕p f = ⊕-elim (⊕-inl ∘g e) (⊕-inr ∘g f)

⊕-swap : A ⊕ B ⊢ B ⊕ A
⊕-swap = ⊕-elim ⊕-inr ⊕-inl

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  where
  opaque
    unfolding ⊕-elim
    ⊕-swap-invol : ⊕-swap ∘g ⊕-swap {A = A}{B = B} ≡ id
    ⊕-swap-invol = ⊕≡ _ _ refl refl

opaque
  unfolding _⊗_ _⊕_
  ⊗⊕-distL :
    A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
  ⊗⊕-distL {A = A} {B = B} {C = C} w (s , p , inl q) = inl (s , p , q)
  ⊗⊕-distL {A = A} {B = B} {C = C} w (s , p , inr q) = inr (s , p , q)

  ⊗⊕-distR :
    (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
  ⊗⊕-distR {A = A} {B = B} {C = C} w (s , inl p , q) = inl (s , p , q)
  ⊗⊕-distR {A = A} {B = B} {C = C} w (s , inr p , q) = inr (s , p , q)

&⊕-distR :
  (A ⊕ B) & C ⊢ (A & C) ⊕ (B & C)
&⊕-distR =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro ⊕-inl)
      (⇒-intro ⊕-inr))

&⊕-distR⁻ :
 (A & B) ⊕ (C & B) ⊢ (A ⊕ C) & B
&⊕-distR⁻ = ⊕-elim (&-par ⊕-inl id) (&-par ⊕-inr id)

open StrongEquivalence

opaque
  unfolding _⊕_ ⇒-intro ⊕-elim
  &⊕-distR-sec : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
    &⊕-distR {A = A}{B = C}{C = B} ∘g &⊕-distR⁻ ≡ id
  &⊕-distR-sec =
    funExt λ w → funExt λ { (inl x) → refl ; (inr x) → refl}
  &⊕-distR-ret : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
    &⊕-distR⁻ ∘g &⊕-distR {A = A}{B = C}{C = B} ≡ id
  &⊕-distR-ret =
    funExt λ w → funExt λ { (inl x , pB) → refl ; (inr x , pB) → refl}

&⊕-distR≅ :
  StrongEquivalence
    ((A ⊕ C) & B)
    ((A & B) ⊕ (C & B))
&⊕-distR≅ .fun = &⊕-distR
&⊕-distR≅ .inv = &⊕-distR⁻
&⊕-distR≅ .sec = &⊕-distR-sec
&⊕-distR≅ .ret = &⊕-distR-ret

&⊕-distL :
  A & (B ⊕ C) ⊢ (A & B) ⊕ (A & C)
&⊕-distL =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro (⊕-inl ∘g &-swap))
      (⇒-intro (⊕-inr ∘g &-swap))) ∘g
  &-swap

&⊕-distL⁻ :
 (A & B) ⊕ (A & C) ⊢ A & (B ⊕ C)
&⊕-distL⁻ = ⊕-elim (&-par id ⊕-inl) (&-par id ⊕-inr)

opaque
  unfolding _⊕_ ⇒-intro ⊕-elim
  &⊕-distL-sec : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
    &⊕-distL {A = A}{B = C}{C = B} ∘g &⊕-distL⁻ ≡ id
  &⊕-distL-sec =
    funExt λ w → funExt λ { (inl x) → refl ; (inr x) → refl}
  &⊕-distL-ret : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
    &⊕-distL⁻ ∘g &⊕-distL {A = A}{B = C}{C = B} ≡ id
  &⊕-distL-ret =
    funExt λ w → funExt λ { (pA , inl x) → refl ; (pA , inr x) → refl}


&⊕-distL≅ :
  StrongEquivalence
    (A & (B ⊕ C))
    ((A & B) ⊕ (A & C))
&⊕-distL≅ .fun = &⊕-distL
&⊕-distL≅ .inv = &⊕-distL⁻
&⊕-distL≅ .sec = &⊕-distL-sec
&⊕-distL≅ .ret = &⊕-distL-ret

open isStrongEquivalence
isMono-⊕-inl : isMono (⊕-inl {A = A} {B = B})
isMono-⊕-inl {A = A}{B = B}{C = C} e e' inl∘e≡inl∘e' =
  sym (&-β₂ _ _) ∙ cong (&-π₂ ∘g_) r ∙ &-β₂ _ _
  where
  isMono-C&A→C&A⊕C&B : isMono (⊕-inl {A = C & A } {B = C & B})
  isMono-C&A→C&A⊕C&B =
    hasRetraction→isMono ⊕-inl (⊕-elim id (id ,& e ∘g &-π₁))
      (⊕-βl id (id ,& e ∘g &-π₁))

  distiso∘inl = (&⊕-distL⁻ ∘g ⊕-inl {A = C & A}{B = C & B})
  isMono-distiso∘inl :
    isMono (&⊕-distL⁻ ∘g ⊕-inl {A = C & A}{B = C & B})
  isMono-distiso∘inl =
    Mono∘g (⊕-inl {A = C & A}{B = C & B}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-C&A→C&A⊕C&B

  p : id ,& (⊕-inl {A = A}{B = B} ∘g e) ≡ id ,& (⊕-inl {A = A}{B = B} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inl∘e≡inl∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim
    q : distiso∘inl ∘g (id ,& e) ≡ distiso∘inl ∘g (id ,& e')
    q = p

  r : (id {A = C} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inl (id ,& e) (id ,& e') q

isMono-⊕-inr : isMono (⊕-inr {A = B} {B = A})
isMono-⊕-inr {B = B}{A = A}{C = C} e e' inr∘e≡inr∘e' =
  sym (&-β₂ _ _) ∙ cong (&-π₂ ∘g_) r ∙ &-β₂ _ _
  where
  isMono-C&B→C&A⊕C&B : isMono (⊕-inr {A = C & B } {B = C & A})
  isMono-C&B→C&A⊕C&B =
    hasRetraction→isMono ⊕-inr
      (⊕-elim (&-π₁ ,& (e ∘g &-π₁)) id)
      (⊕-βr (&-π₁ ,& (e ∘g &-π₁)) id)

  distiso∘inr = (&⊕-distL⁻ ∘g ⊕-inr {A = C & B}{B = C & A})
  isMono-distiso∘inr :
    isMono (&⊕-distL⁻ ∘g ⊕-inr {A = C & B}{B = C & A})
  isMono-distiso∘inr =
    Mono∘g (⊕-inr {A = C & B}{B = C & A}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-C&B→C&A⊕C&B

  p : id ,& (⊕-inr {A = B}{B = A} ∘g e) ≡ id ,& (⊕-inr {A = B}{B = A} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inr∘e≡inr∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim
    q : distiso∘inr ∘g id ,& e ≡ distiso∘inr ∘g id ,& e'
    q = p

  r : (id {A = C} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inr (id ,& e) (id ,& e') q

module InductiveSum (A : Grammar ℓA) (B : Grammar ℓB) where
  open import Grammar.Inductive.Indexed Alphabet as Inductive
  open import Grammar.Dependent.Base Alphabet
  open import Grammar.Lift Alphabet
  open import Cubical.Data.Unit
  open import Cubical.Data.FinSet

  data ⊕IndTag : Type (ℓ-max ℓA ℓB) where
    L R : ⊕IndTag

  ⊕IndTagRep : Iso (Fin 2) ⊕IndTag
  ⊕IndTagRep =
      (iso
        (λ { (inl tt) → L ; (inr (inl tt)) → R})
        (λ { L → inl tt ; R → inr (inl tt)})
        (λ { L → refl ; R → refl})
        λ { (inl tt) → refl ; (inr (inl tt)) → refl}
        )

  isFinSet⊕IndTag : isFinSet ⊕IndTag
  isFinSet⊕IndTag =
    EquivPresIsFinSet
      (isoToEquiv ⊕IndTagRep)
      (isFinSetFin {n = 2})

  open Iso
  L≢R : L ≡ R → Empty.⊥
  L≢R L≡R = fzero≠fone (cong (⊕IndTagRep .inv) L≡R)

  ⊕IndTy : Unit* {ℓ-max ℓA ℓB} → Functor Unit*
  ⊕IndTy _ = ⊕e ⊕IndTag λ {
      L → Inductive.k (LiftG ℓB A)
    ; R → Inductive.k (LiftG ℓA B)}

  ⊕Ind : Grammar (ℓ-max ℓA ℓB)
  ⊕Ind = μ ⊕IndTy _

  ⊕Ind→⊕Alg : Algebra ⊕IndTy λ _ → A ⊕ B
  ⊕Ind→⊕Alg _ = ⊕ᴰ-elim (λ {
      L → ⊕-inl ∘g lowerG ∘g lowerG
    ; R → ⊕-inr ∘g lowerG ∘g lowerG })

  ⊕Ind→⊕ : ⊕Ind ⊢ A ⊕ B
  ⊕Ind→⊕ = Inductive.rec ⊕IndTy ⊕Ind→⊕Alg _

  ⊕Ind' : Grammar (ℓ-max ℓA ℓB)
  ⊕Ind' = ⟦ ⊕IndTy _ ⟧ λ _ → ⊕Ind

  open import Grammar.Inductive.Properties Alphabet
  unroll⊕Ind≅ : ⊕Ind ≅ ⊕Ind'
  unroll⊕Ind≅ = unroll≅ ⊕IndTy _

  opaque
    unfolding _⊕_ ⊕-elim
    ⊕≅⊕Ind : StrongEquivalence (A ⊕ B) ⊕Ind
    ⊕≅⊕Ind =
      mkStrEq
        (⊕-elim
          (roll ∘g ⊕ᴰ-in L ∘g liftG ∘g liftG)
          (roll ∘g ⊕ᴰ-in R ∘g liftG ∘g liftG)
        )
        ⊕Ind→⊕
        (ind' ⊕IndTy (initialAlgebra ⊕IndTy)
          (_ ,
          λ _ → ⊕ᴰ≡ _ _
            λ { L → refl ; R → refl})
          (idHomo ⊕IndTy _)
          _)
        (⊕≡ _ _ refl refl)

module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  {C : Grammar ℓC} {D : Grammar ℓD}
  (A≅B : A ≅ B)
  (C≅D : C ≅ D)
  where

  private
    the-fun : A ⊕ C ⊢ B ⊕ D
    the-fun = A≅B .fun ,⊕p C≅D .fun

    the-inv : B ⊕ D ⊢ A ⊕ C
    the-inv = A≅B .inv ,⊕p C≅D .inv
    opaque
      unfolding _⊕_ ⊕-elim
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec =
        ⊕≡ _ _
          (cong (⊕-inl ∘g_) (A≅B .sec))
          (cong (⊕-inr ∘g_) (C≅D .sec))
      the-ret : the-inv ∘g the-fun ≡ id
      the-ret =
        ⊕≡ _ _
          (cong (⊕-inl ∘g_) (A≅B .ret))
          (cong (⊕-inr ∘g_) (C≅D .ret))

  ⊕≅ : (A ⊕ C) ≅ (B ⊕ D)
  ⊕≅ .fun = the-fun
  ⊕≅ .inv = the-inv
  ⊕≅ .sec = the-sec
  ⊕≅ .ret = the-ret

module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  where
  ⊕-swap≅ : (A ⊕ B) ≅ (B ⊕ A)
  ⊕-swap≅ .fun = ⊕-swap
  ⊕-swap≅ .inv = ⊕-swap
  ⊕-swap≅ .sec = ⊕-swap-invol
  ⊕-swap≅ .ret = ⊕-swap-invol

module _
  {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
  where

  ⊕-assoc : (A ⊕ B) ⊕ C ⊢ A ⊕ (B ⊕ C)
  ⊕-assoc = ⊕-elim (⊕-elim ⊕-inl (⊕-inr ∘g ⊕-inl)) (⊕-inr ∘g ⊕-inr)

  ⊕-assoc⁻ : A ⊕ (B ⊕ C) ⊢ (A ⊕ B) ⊕ C
  ⊕-assoc⁻ = ⊕-elim (⊕-inl ∘g ⊕-inl) (⊕-elim (⊕-inl ∘g ⊕-inr) ⊕-inr)

  private
    opaque
      unfolding _⊕_ ⊕-elim
      the-sec : ⊕-assoc ∘g ⊕-assoc⁻ ≡ id
      the-sec = ⊕≡ _ _ refl (⊕≡ _ _ refl refl)
      the-ret : ⊕-assoc⁻ ∘g ⊕-assoc ≡ id
      the-ret = ⊕≡ _ _ (⊕≡ _ _ refl refl) refl

  ⊕-assoc≅ : (A ⊕ B) ⊕ C ≅ A ⊕ (B ⊕ C)
  ⊕-assoc≅ .fun = ⊕-assoc
  ⊕-assoc≅ .inv = ⊕-assoc⁻
  ⊕-assoc≅ .sec = the-sec
  ⊕-assoc≅ .ret = the-ret

