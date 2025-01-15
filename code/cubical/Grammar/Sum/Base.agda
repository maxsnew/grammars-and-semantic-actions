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
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_⊕'_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊕' h) w = g w ⊎ h w
infixr 5 _⊕'_
opaque
  _⊕_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  _⊕_ = _⊕'_

infixr 5 _⊕_

opaque
  unfolding _⊕_
  ⊕-inl :
    g ⊢ g ⊕ h
  ⊕-inl _ p = inl p


  ⊕-inr :
    g ⊢ h ⊕ g
  ⊕-inr _ p = inr p

  ⊕-elim :
    g ⊢ h →
    k ⊢ h →
    g ⊕ k ⊢ h
  ⊕-elim eg eh _ p =
    Sum.elim
      (λ pg → eg _ pg)
      (λ ph → eh _ ph)
      p

  ⊕≡ :
    (f f' : g ⊕ k ⊢ h)
    → (f ∘g ⊕-inl ≡ f' ∘g ⊕-inl)
    → (f ∘g ⊕-inr ≡ f' ∘g ⊕-inr)
    → f ≡ f'
  ⊕≡ f f' f≡f'inl f≡f'inr = funExt λ w → funExt λ
    { (inl x) → funExt⁻ (funExt⁻ f≡f'inl _) x
    ; (inr x) → funExt⁻ (funExt⁻ f≡f'inr _) x }

  ⊕-βl :
    (e₁ : g ⊢ k) →
    (e₂ : h ⊢ k) →
    ⊕-inl ⋆ ⊕-elim e₁ e₂
      ≡
    e₁
  ⊕-βl e₁ e₂ = refl

  ⊕-βr :
    (e₁ : g ⊢ k) →
    (e₂ : h ⊢ k) →
    ⊕-inr ⋆ ⊕-elim e₁ e₂
      ≡
    e₂
  ⊕-βr e₁ e₂ = refl

  ⊕-η :
    (e : g ⊕ h ⊢ k) →
    (⊕-elim {g = g}{h = k}{k = h}
      (e ∘g ⊕-inl)
      (e ∘g ⊕-inr)
    )
      ≡
      e
  ⊕-η e i _ (inl x) = e _ (inl x)
  ⊕-η e i _ (inr x) = e _ (inr x)

_,⊕p_ :
  g ⊢ h →
  k ⊢ l →
  g ⊕ k ⊢ h ⊕ l
e ,⊕p f = ⊕-elim (⊕-inl ∘g e) (⊕-inr ∘g f)

⊕-swap : g ⊕ h ⊢ h ⊕ g
⊕-swap = ⊕-elim ⊕-inr ⊕-inl

module _
  {g : Grammar ℓg}
  {h : Grammar ℓh}
  where
  opaque
    unfolding ⊕-elim
    ⊕-swap-invol : ⊕-swap ∘g ⊕-swap {g = g}{h = h} ≡ id
    ⊕-swap-invol = ⊕≡ _ _ refl refl

opaque
  unfolding _⊗_ _⊕_
  ⊗⊕-distL :
    g ⊗ (h ⊕ k) ⊢ (g ⊗ h) ⊕ (g ⊗ k)
  ⊗⊕-distL {g = g} {h = h} {k = k} w (s , p , inl q) = inl (s , p , q)
  ⊗⊕-distL {g = g} {h = h} {k = k} w (s , p , inr q) = inr (s , p , q)

  ⊗⊕-distR :
    (g ⊕ h) ⊗ k ⊢ (g ⊗ k) ⊕ (h ⊗ k)
  ⊗⊕-distR {g = g} {h = h} {k = k} w (s , inl p , q) = inl (s , p , q)
  ⊗⊕-distR {g = g} {h = h} {k = k} w (s , inr p , q) = inr (s , p , q)

&⊕-distR :
  (g ⊕ h) & k ⊢ (g & k) ⊕ (h & k)
&⊕-distR =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro ⊕-inl)
      (⇒-intro ⊕-inr))

&⊕-distR⁻ :
 (g & h) ⊕ (k & h) ⊢ (g ⊕ k) & h
&⊕-distR⁻ = ⊕-elim (&-par ⊕-inl id) (&-par ⊕-inr id)

open StrongEquivalence

opaque
  unfolding _⊕_ ⇒-intro ⊕-elim
  &⊕-distR-sec : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk} →
    &⊕-distR {g = g}{h = k}{k = h} ∘g &⊕-distR⁻ ≡ id
  &⊕-distR-sec =
    funExt λ w → funExt λ { (inl x) → refl ; (inr x) → refl}
  &⊕-distR-ret : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk} →
    &⊕-distR⁻ ∘g &⊕-distR {g = g}{h = k}{k = h} ≡ id
  &⊕-distR-ret =
    funExt λ w → funExt λ { (inl x , ph) → refl ; (inr x , ph) → refl}

&⊕-distR≅ :
  StrongEquivalence
    ((g ⊕ k) & h)
    ((g & h) ⊕ (k & h))
&⊕-distR≅ .fun = &⊕-distR
&⊕-distR≅ .inv = &⊕-distR⁻
&⊕-distR≅ .sec = &⊕-distR-sec
&⊕-distR≅ .ret = &⊕-distR-ret

&⊕-distL :
  g & (h ⊕ k) ⊢ (g & h) ⊕ (g & k)
&⊕-distL =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro (⊕-inl ∘g &-swap))
      (⇒-intro (⊕-inr ∘g &-swap))) ∘g
  &-swap

&⊕-distL⁻ :
 (g & h) ⊕ (g & k) ⊢ g & (h ⊕ k)
&⊕-distL⁻ = ⊕-elim (&-par id ⊕-inl) (&-par id ⊕-inr)

opaque
  unfolding _⊕_ ⇒-intro ⊕-elim
  &⊕-distL-sec : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk} →
    &⊕-distL {g = g}{h = k}{k = h} ∘g &⊕-distL⁻ ≡ id
  &⊕-distL-sec =
    funExt λ w → funExt λ { (inl x) → refl ; (inr x) → refl}
  &⊕-distL-ret : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk} →
    &⊕-distL⁻ ∘g &⊕-distL {g = g}{h = k}{k = h} ≡ id
  &⊕-distL-ret =
    funExt λ w → funExt λ { (pg , inl x) → refl ; (pg , inr x) → refl}


&⊕-distL≅ :
  StrongEquivalence
    (g & (h ⊕ k))
    ((g & h) ⊕ (g & k))
&⊕-distL≅ .fun = &⊕-distL
&⊕-distL≅ .inv = &⊕-distL⁻
&⊕-distL≅ .sec = &⊕-distL-sec
&⊕-distL≅ .ret = &⊕-distL-ret

open isStrongEquivalence
isMono-⊕-inl : isMono (⊕-inl {g = g} {h = h})
isMono-⊕-inl {g = g}{h = h}{k = k} e e' inl∘e≡inl∘e' =
  sym (&-β₂ _ _) ∙ cong (&-π₂ ∘g_) r ∙ &-β₂ _ _
  where
  isMono-k&g→k&g⊕k&h : isMono (⊕-inl {g = k & g } {h = k & h})
  isMono-k&g→k&g⊕k&h =
    hasRetraction→isMono ⊕-inl (⊕-elim id (id ,& e ∘g &-π₁))
      (⊕-βl id (id ,& e ∘g &-π₁))

  distiso∘inl = (&⊕-distL⁻ ∘g ⊕-inl {g = k & g}{h = k & h})
  isMono-distiso∘inl :
    isMono (&⊕-distL⁻ ∘g ⊕-inl {g = k & g}{h = k & h})
  isMono-distiso∘inl =
    Mono∘g (⊕-inl {g = k & g}{h = k & h}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-k&g→k&g⊕k&h

  p : id ,& (⊕-inl {g = g}{h = h} ∘g e) ≡ id ,& (⊕-inl {g = g}{h = h} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inl∘e≡inl∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim
    q : distiso∘inl ∘g (id ,& e) ≡ distiso∘inl ∘g (id ,& e')
    q = p

  r : (id {g = k} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inl (id ,& e) (id ,& e') q

isMono-⊕-inr : isMono (⊕-inr {g = h} {h = g})
isMono-⊕-inr {h = h}{g = g}{k = k} e e' inr∘e≡inr∘e' =
  sym (&-β₂ _ _) ∙ cong (&-π₂ ∘g_) r ∙ &-β₂ _ _
  where
  isMono-k&h→k&g⊕k&h : isMono (⊕-inr {g = k & h } {h = k & g})
  isMono-k&h→k&g⊕k&h =
    hasRetraction→isMono ⊕-inr
      (⊕-elim (&-π₁ ,& (e ∘g &-π₁)) id)
      (⊕-βr (&-π₁ ,& (e ∘g &-π₁)) id)

  distiso∘inr = (&⊕-distL⁻ ∘g ⊕-inr {g = k & h}{h = k & g})
  isMono-distiso∘inr :
    isMono (&⊕-distL⁻ ∘g ⊕-inr {g = k & h}{h = k & g})
  isMono-distiso∘inr =
    Mono∘g (⊕-inr {g = k & h}{h = k & g}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-k&h→k&g⊕k&h

  p : id ,& (⊕-inr {g = h}{h = g} ∘g e) ≡ id ,& (⊕-inr {g = h}{h = g} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inr∘e≡inr∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim
    q : distiso∘inr ∘g id ,& e ≡ distiso∘inr ∘g id ,& e'
    q = p

  r : (id {g = k} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inr (id ,& e) (id ,& e') q

module InductiveSum (g : Grammar ℓg) (h : Grammar ℓh) where
  open import Grammar.Inductive.Indexed Alphabet as Inductive
  open import Grammar.Dependent.Base Alphabet
  open import Grammar.Lift Alphabet
  open import Cubical.Data.Unit
  open import Cubical.Data.FinSet

  data ⊕IndTag : Type (ℓ-max ℓg ℓh) where
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

  ⊕IndTy : Unit* {ℓ-max ℓg ℓh} → Functor Unit*
  ⊕IndTy _ = ⊕e ⊕IndTag λ {
      L → Inductive.k (LiftG ℓh g)
    ; R → Inductive.k (LiftG ℓg h)}

  ⊕Ind : Grammar (ℓ-max ℓg ℓh)
  ⊕Ind = μ ⊕IndTy _

  ⊕Ind→⊕Alg : Algebra ⊕IndTy λ _ → g ⊕ h
  ⊕Ind→⊕Alg _ = ⊕ᴰ-elim (λ {
      L → ⊕-inl ∘g lowerG ∘g lowerG
    ; R → ⊕-inr ∘g lowerG ∘g lowerG })

  ⊕Ind→⊕ : ⊕Ind ⊢ g ⊕ h
  ⊕Ind→⊕ = Inductive.rec ⊕IndTy ⊕Ind→⊕Alg _

  ⊕Ind' : Grammar (ℓ-max ℓg ℓh)
  ⊕Ind' = ⟦ ⊕IndTy _ ⟧ λ _ → ⊕Ind

  open import Grammar.Inductive.Properties Alphabet
  unroll⊕Ind≅ : ⊕Ind ≅ ⊕Ind'
  unroll⊕Ind≅ = unroll≅ ⊕IndTy _

  opaque
    unfolding _⊕_ ⊕-elim
    ⊕≅⊕Ind : StrongEquivalence (g ⊕ h) ⊕Ind
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
  {g : Grammar ℓg} {h : Grammar ℓh}
  {k : Grammar ℓk} {l : Grammar ℓl}
  (g≅h : g ≅ h)
  (k≅l : k ≅ l)
  where

  private
    the-fun : g ⊕ k ⊢ h ⊕ l
    the-fun = g≅h .fun ,⊕p k≅l .fun

    the-inv : h ⊕ l ⊢ g ⊕ k
    the-inv = g≅h .inv ,⊕p k≅l .inv
    opaque
      unfolding _⊕_ ⊕-elim
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec =
        ⊕≡ _ _
          (cong (⊕-inl ∘g_) (g≅h .sec))
          (cong (⊕-inr ∘g_) (k≅l .sec))
      the-ret : the-inv ∘g the-fun ≡ id
      the-ret =
        ⊕≡ _ _
          (cong (⊕-inl ∘g_) (g≅h .ret))
          (cong (⊕-inr ∘g_) (k≅l .ret))

  ⊕≅ : (g ⊕ k) ≅ (h ⊕ l)
  ⊕≅ .fun = the-fun
  ⊕≅ .inv = the-inv
  ⊕≅ .sec = the-sec
  ⊕≅ .ret = the-ret

module _
  {g : Grammar ℓg} {h : Grammar ℓh}
  where
  ⊕-swap≅ : (g ⊕ h) ≅ (h ⊕ g)
  ⊕-swap≅ .fun = ⊕-swap
  ⊕-swap≅ .inv = ⊕-swap
  ⊕-swap≅ .sec = ⊕-swap-invol
  ⊕-swap≅ .ret = ⊕-swap-invol

module _
  {g : Grammar ℓg} {h : Grammar ℓh} {k : Grammar ℓk}
  where

  ⊕-assoc : (g ⊕ h) ⊕ k ⊢ g ⊕ (h ⊕ k)
  ⊕-assoc = ⊕-elim (⊕-elim ⊕-inl (⊕-inr ∘g ⊕-inl)) (⊕-inr ∘g ⊕-inr)

  ⊕-assoc⁻ : g ⊕ (h ⊕ k) ⊢ (g ⊕ h) ⊕ k
  ⊕-assoc⁻ = ⊕-elim (⊕-inl ∘g ⊕-inl) (⊕-elim (⊕-inl ∘g ⊕-inr) ⊕-inr)

  private
    opaque
      unfolding _⊕_ ⊕-elim
      the-sec : ⊕-assoc ∘g ⊕-assoc⁻ ≡ id
      the-sec = ⊕≡ _ _ refl (⊕≡ _ _ refl refl)
      the-ret : ⊕-assoc⁻ ∘g ⊕-assoc ≡ id
      the-ret = ⊕≡ _ _ (⊕≡ _ _ refl refl) refl

  ⊕-assoc≅ : (g ⊕ h) ⊕ k ≅ g ⊕ (h ⊕ k)
  ⊕-assoc≅ .fun = ⊕-assoc
  ⊕-assoc≅ .inv = ⊕-assoc⁻
  ⊕-assoc≅ .sec = the-sec 
  ⊕-assoc≅ .ret = the-ret
