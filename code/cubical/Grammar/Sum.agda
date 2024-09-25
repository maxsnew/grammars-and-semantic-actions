open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum

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

opaque
  _⊕_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  (g ⊕ h) w = g w ⊎ h w

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

⊗⊕-distL :
  g ⊗ (h ⊕ k) ⊢ (g ⊗ h) ⊕ (g ⊗ k)
⊗⊕-distL {g = g}{h = h}{k = k} =
  ⊸-intro⁻ {g = h ⊕ k}{h = g}{k = (g ⊗ h) ⊕ (g ⊗ k)}
    (⊕-elim {g = h}{h = g ⊸ ((g ⊗ h) ⊕ (g ⊗ k))}{k = k}
      (⊸-intro {g = g}{h = h}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inl)
      (⊸-intro {g = g}{h = k}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inr))

⊗⊕-distR :
  (g ⊕ h) ⊗ k ⊢ (g ⊗ k) ⊕ (h ⊗ k)
⊗⊕-distR {g = g}{h = h}{k = k} =
  ⟜-intro⁻
    (⊕-elim (⟜-intro (⊕-inl {h = h ⊗ k}))
    (⟜-intro (⊕-inr {h = g ⊗ k})))

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
