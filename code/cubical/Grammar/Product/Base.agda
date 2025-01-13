open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open StrongEquivalence

_&'_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g &' h) w = g w × h w
infixr 6 _&'_
opaque
  _&_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  _&_ = _&'_

infixr 6 _&_

opaque
  unfolding _&_
  &-intro :
    g ⊢ h →
    g ⊢ k →
    g ⊢ h & k
  &-intro e e' _ p =
    e _ p , e' _ p

  &-π₁ :
    g & h ⊢ g
  &-π₁ _ p = p .fst

  &-π₂ :
    g & h ⊢ h
  &-π₂ _ p = p .snd

  &-β₁ :
    (e₁ : g ⊢ h) →
    (e₂ : g ⊢ k) →
    &-π₁ ∘g (&-intro e₁ e₂)
      ≡
    e₁
  &-β₁ e₁ e₂ = refl

  &-β₂ :
    (e₁ : g ⊢ h) →
    (e₂ : g ⊢ k) →
    &-π₂ ∘g (&-intro e₁ e₂)
      ≡
    e₂
  &-β₂ e₁ e₂ = refl

  &-η :
    (e : g ⊢ h & k) →
    (&-intro {g = g}{h = h}{k = k}
      (&-π₁ ∘g e)
      (&-π₂ ∘g e))
    ≡
    e
  &-η e = refl

  &-η' :
   (e e' : g ⊢ h & k) →
   &-π₁ ∘g e ≡ &-π₁ ∘g e' →
   &-π₂ ∘g e ≡ &-π₂ ∘g e' →
   e ≡ e'
  &-η' e e' p₁ p₂ =
    sym (&-η e) ∙ cong₂ &-intro p₁ p₂ ∙ &-η e'

  &≡ :
    (f f' : g  ⊢ h & k) →
    &-π₁ ∘g f ≡ &-π₁ ∘g f' →
    &-π₂ ∘g f ≡ &-π₂ ∘g f' →
    f ≡ f'
  &≡ f f' π₁≡ π₂≡ = funExt (λ w → funExt (λ p →
    λ i → π₁≡ i w p , π₂≡ i w p))

_,&_ = &-intro
infixr 20 _,&_

&par : g ⊢ h → k ⊢ l → g & k ⊢ h & l
&par f f' = (f ∘g &-π₁) ,& (f' ∘g &-π₂)

_,&p_ = &par
infixr 20 _,&p_

id&_ : h ⊢ k → g & h ⊢ g & k
id& f = &-π₁ ,& (f ∘g &-π₂)

&-swap :
  g & h ⊢ h & g
&-swap = &-intro &-π₂ &-π₁

module _
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  where
  opaque
    unfolding &-intro
    &-swap-invol : &-swap ∘g &-swap {g = g}{h = h} ≡ id
    &-swap-invol = refl

&-assoc :
  g & (h & k) ⊢ (g & h) & k
&-assoc = &-intro (&-intro &-π₁ (&-π₁ ∘g &-π₂)) (&-π₂ ∘g &-π₂)

&-assoc⁻ :
  (g & h) & k ⊢ g & (h & k)
&-assoc⁻ = &-intro (&-π₁ ∘g &-π₁) (&-intro (&-π₂ ∘g &-π₁) &-π₂)

&-par :
  g ⊢ h → k ⊢ l →
  g & k ⊢ h & l
&-par e e' = &-intro (e ∘g &-π₁) (e' ∘g &-π₂)

⊗&-distL :
  g ⊗ (h & k) ⊢ (g ⊗ h) & (g ⊗ k)
⊗&-distL = &-intro (⊗-intro id &-π₁) (⊗-intro id &-π₂)

⊗&-distR :
  (g & h) ⊗ k ⊢ (g ⊗ k) & (h ⊗ k)
⊗&-distR = &-intro (⊗-intro &-π₁ id) (⊗-intro &-π₂ id)

module InductiveProduct (g : Grammar ℓg) (h : Grammar ℓh) where
  open import Grammar.Inductive.Indexed Alphabet as Inductive
  open import Grammar.Dependent.Base Alphabet
  open import Grammar.Lift Alphabet
  open import Cubical.Data.Unit
  open import Cubical.Data.FinSet

  data &IndTag : Type (ℓ-max ℓg ℓh) where
    L R : &IndTag

  isFinSet&IndTag : isFinSet &IndTag
  isFinSet&IndTag =
    EquivPresIsFinSet
      (isoToEquiv (iso
        (λ { (inl tt) → L ; (inr (inl tt)) → R})
        (λ { L → inl tt ; R → inr (inl tt)})
        (λ { L → refl ; R → refl})
        λ { (inl tt) → refl ; (inr (inl tt)) → refl}
        ))
      (isFinSetFin {n = 2})

  &IndTy : Unit* {ℓ-max ℓg ℓh} → Functor Unit*
  &IndTy _ = &e &IndTag λ {
      L → Inductive.k (LiftG ℓh g)
    ; R → Inductive.k (LiftG ℓg h)}

  &Ind : Grammar (ℓ-max ℓg ℓh)
  &Ind = μ &IndTy _

  opaque
    unfolding _&_
    &Ind→&Alg : Algebra &IndTy λ _ → g & h
    &Ind→&Alg _ = (lowerG ∘g lowerG ∘g &ᴰ-π L) ,& (lowerG ∘g lowerG ∘g &ᴰ-π R)

  &Ind→& : &Ind ⊢ g & h
  &Ind→& = Inductive.rec &IndTy &Ind→&Alg _

  &Ind' : Grammar (ℓ-max ℓg ℓh)
  &Ind' = ⟦ &IndTy _ ⟧ λ _ → &Ind

  open import Grammar.Inductive.Properties Alphabet
  unroll&Ind≅ : &Ind ≅ &Ind'
  unroll&Ind≅ = unroll≅ &IndTy _

  opaque
    unfolding _&_ &-π₁
    &≅&Ind' : StrongEquivalence (g & h) &Ind'
    &≅&Ind' =
      mkStrEq
        (&ᴰ-in (λ {
          L → liftG ∘g liftG ∘g &-π₁
        ; R → liftG ∘g liftG ∘g &-π₂
        }))
        ((lowerG ∘g lowerG ∘g &ᴰ-π L) ,& (lowerG ∘g lowerG ∘g &ᴰ-π R))
        (&ᴰ≡ _ _ (λ {
          L → refl
        ; R → refl
        }))
        refl

  &≅&Ind : StrongEquivalence (g & h) &Ind
  &≅&Ind = &≅&Ind' ≅∙ sym≅ unroll&Ind≅

module _
  {g : Grammar ℓg} {h : Grammar ℓh}
  {k : Grammar ℓk} {l : Grammar ℓl}
  (g≅h : g ≅ h)
  (k≅l : k ≅ l)
  where

  private
    the-fun : g & k ⊢ h & l
    the-fun = g≅h .fun ,&p k≅l .fun

    the-inv : h & l ⊢ g & k
    the-inv = g≅h .inv ,&p k≅l .inv
    opaque
      unfolding _&_ &-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec =
        &≡ _ _
          (cong (_∘g &-π₁) (g≅h .sec))
          (cong (_∘g &-π₂) (k≅l .sec))
      the-ret : the-inv ∘g the-fun ≡ id
      the-ret =
        &≡ _ _
          (cong (_∘g &-π₁) (g≅h .ret))
          (cong (_∘g &-π₂) (k≅l .ret))

  &≅ : (g & k) ≅ (h & l)
  &≅ .fun = the-fun
  &≅ .inv = the-inv
  &≅ .sec = the-sec
  &≅ .ret = the-ret

module _
  {g : Grammar ℓg} {h : Grammar ℓh}
  where
  &-swap≅ : g & h ≅ h & g
  &-swap≅ .fun = &-swap
  &-swap≅ .inv = &-swap
  &-swap≅ .sec = &-swap-invol
  &-swap≅ .ret = &-swap-invol
