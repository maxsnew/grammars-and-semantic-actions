open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Binary.Cartesian.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

opaque
  _&_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A & B) w = A w × B w

infixr 27 _&_

opaque
  unfolding _&_
  &-intro :
    A ⊢ B →
    A ⊢ C →
    A ⊢ B & C
  &-intro e e' _ p =
    e _ p , e' _ p

_,&_ = &-intro
infixr 20 _,&_

opaque
  unfolding _&_ &-intro
  π₁ : A & B ⊢ A
  π₁ _ p = p .fst

  π₂ : A & B ⊢ B
  π₂ _ p = p .snd

  &-β₁ : (e₁ : A ⊢ B) → (e₂ : A ⊢ C) →
    π₁ ∘g (e₁ ,& e₂) ≡ e₁
  &-β₁ e₁ e₂ = refl

  &-β₂ : (e₁ : A ⊢ B) → (e₂ : A ⊢ C) →
    π₂ ∘g (e₁ ,& e₂) ≡ e₂
  &-β₂ e₁ e₂ = refl

  &-η : (e : A ⊢ B & C) → (π₁ ∘g e) ,& (π₂ ∘g e) ≡ e
  &-η e = refl

  &-η' : (e e' : A ⊢ B & C) →
   π₁ ∘g e ≡ π₁ ∘g e' → π₂ ∘g e ≡ π₂ ∘g e' →
   e ≡ e'
  &-η' e e' p₁ p₂ =
    sym (&-η e) ∙ cong₂ &-intro p₁ p₂ ∙ &-η e'

  &≡ : (f f' : A  ⊢ B & C) →
    π₁ ∘g f ≡ π₁ ∘g f' → π₂ ∘g f ≡ π₂ ∘g f' →
    f ≡ f'
  &≡ f f' π₁≡ π₂≡ = funExt (λ w → funExt (λ p →
    λ i → π₁≡ i w p , π₂≡ i w p))

&par : A ⊢ B → C ⊢ D → A & C ⊢ B & D
&par f f' = (f ∘g π₁) ,& (f' ∘g π₂)

_,&p_ = &par
infixr 20 _,&p_

id&_ : B ⊢ C → A & B ⊢ A & C
id& f = π₁ ,& (f ∘g π₂)

&-swap : A & B ⊢ B & A
&-swap = π₂ ,& π₁

&-Δ : A ⊢ A & A
&-Δ = id ,& id

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  where
  opaque
    unfolding &-intro π₁
    &-swap-invol : &-swap ∘g &-swap {A = A}{B = B} ≡ id
    &-swap-invol = refl

&-assoc : A & (B & C) ⊢ (A & B) & C
&-assoc = &-intro (π₁ ,& (π₁ ∘g π₂)) (π₂ ∘g π₂)

&-assoc⁻ : (A & B) & C ⊢ A & (B & C)
&-assoc⁻ = &-intro (π₁ ∘g π₁) ((π₂ ∘g π₁) ,& π₂)

&-par : A ⊢ B → C ⊢ D → A & C ⊢ B & D
&-par e e' = (e ∘g π₁) ,& (e' ∘g π₂)

⊗&-distL : A ⊗ (B & C) ⊢ (A ⊗ B) & (A ⊗ C)
⊗&-distL = (id ,⊗ π₁) ,& (id ,⊗ π₂)

⊗&-distR : (A & B) ⊗ C ⊢ (A ⊗ C) & (B ⊗ C)
⊗&-distR = (π₁ ,⊗ id) ,& (π₂ ,⊗ id)

-- TODO : use Product.Binary.Inductive
-- module InductiveProduct (A : Grammar ℓA) (B : Grammar ℓB) where
--   open import Grammar.Inductive.Indexed Alphabet as Inductive
--   open import Grammar.Dependent.Base Alphabet
--   open import Grammar.Lift Alphabet
--   open import Cubical.Data.Unit
--   open import Cubical.Data.FinSet

--   data &IndTag : Type (ℓ-max ℓA ℓB) where
--     L R : &IndTag

--   isFinSet&IndTag : isFinSet &IndTag
--   isFinSet&IndTag =
--     EquivPresIsFinSet
--       (isoToEquiv (iso
--         (λ { (inl tt) → L ; (inr (inl tt)) → R})
--         (λ { L → inl tt ; R → inr (inl tt)})
--         (λ { L → refl ; R → refl})
--         λ { (inl tt) → refl ; (inr (inl tt)) → refl}
--         ))
--       (isFinSetFin {n = 2})

--   &IndTy : Unit* {ℓ-max ℓA ℓB} → Functor Unit*
--   &IndTy _ = &e &IndTag λ {
--       L → Inductive.k (LiftG ℓB A)
--     ; R → Inductive.k (LiftG ℓA B)}

--   &Ind : Grammar (ℓ-max ℓA ℓB)
--   &Ind = μ &IndTy _

--   opaque
--     unfolding _&_
--     &Ind→&Alg : Algebra &IndTy λ _ → A & B
--     &Ind→&Alg _ = (lowerG ∘g lowerG ∘g &ᴰ-π L) ,& (lowerG ∘g lowerG ∘g &ᴰ-π R)

--   &Ind→& : &Ind ⊢ A & B
--   &Ind→& = Inductive.rec &IndTy &Ind→&Alg _

--   &Ind' : Grammar (ℓ-max ℓA ℓB)
--   &Ind' = ⟦ &IndTy _ ⟧ λ _ → &Ind

--   open import Grammar.Inductive.Properties Alphabet
--   unroll&Ind≅ : &Ind ≅ &Ind'
--   unroll&Ind≅ = unroll≅ &IndTy _

--   opaque
--     unfolding _&_ &-π₁
--     &≅&Ind' : StrongEquivalence (A & B) &Ind'
--     &≅&Ind' =
--       mkStrEq
--         (&ᴰ-in (λ {
--           L → liftG ∘g liftG ∘g &-π₁
--         ; R → liftG ∘g liftG ∘g &-π₂
--         }))
--         ((lowerG ∘g lowerG ∘g &ᴰ-π L) ,& (lowerG ∘g lowerG ∘g &ᴰ-π R))
--         (&ᴰ≡ _ _ (λ {
--           L → refl
--         ; R → refl
--         }))
--         refl

--   &≅&Ind : StrongEquivalence (A & B) &Ind
--   &≅&Ind = &≅&Ind' ≅∙ sym≅ unroll&Ind≅

module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  {C : Grammar ℓC} {D : Grammar ℓD}
  (A≅B : A ≅ B)
  (C≅D : C ≅ D)
  where

  private
    the-fun : A & C ⊢ B & D
    the-fun = A≅B .fun ,&p C≅D .fun

    the-inv : B & D ⊢ A & C
    the-inv = A≅B .inv ,&p C≅D .inv
    opaque
      unfolding _&_ &-intro π₁
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec =
        &≡ _ _
          (cong (_∘g π₁) (A≅B .sec))
          (cong (_∘g π₂) (C≅D .sec))
      the-ret : the-inv ∘g the-fun ≡ id
      the-ret =
        &≡ _ _
          (cong (_∘g π₁) (A≅B .ret))
          (cong (_∘g π₂) (C≅D .ret))

  &≅ : (A & C) ≅ (B & D)
  &≅ .fun = the-fun
  &≅ .inv = the-inv
  &≅ .sec = the-sec
  &≅ .ret = the-ret

module _
  {A : Grammar ℓA} {B : Grammar ℓB}
  where
  &-swap≅ : A & B ≅ B & A
  &-swap≅ .fun = &-swap
  &-swap≅ .inv = &-swap
  &-swap≅ .sec = &-swap-invol
  &-swap≅ .ret = &-swap-invol
