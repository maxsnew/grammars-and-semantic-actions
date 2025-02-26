open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.LinearFunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Term.Bilinear Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A A1 : Grammar ℓA
    B A2 : Grammar ℓB
    C A3 : Grammar ℓC
    D A4 : Grammar ℓD
    f f' f'' : A ⊢ B

opaque
  unfolding _⊗_
  _⟜_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⟜ B) w = ∀ (w' : String) → B w' → A (w' ++ w)

  _⊸_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⊸ B) w = ∀ (w' : String) → A w' → B (w ++ w')

  infixr 2 _⊸_
  infixl 2 _⟜_

  ⟜-intro :
    A ⊗ B ⊢ C →
    B ⊢ C ⟜ A
  ⟜-intro e _ p w' q =
    e _ ((_ , refl) , (q , p))

  ⟜-app :
    A ⊗ (B ⟜ A) ⊢ B
  ⟜-app {B = B} _ p = subst B (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

  ⟜-intro' :
    A ,, B ⊢ C →
    B ⊢ C ⟜ A
  ⟜-intro' f w' p w q = f w w' q p

  ⟜-app' :
    A ,, (B ⟜ A) ⊢ B
  ⟜-app' w1 w2 Ap f = f w1 Ap

--   -- this makes me think we don't want ⟜-app' and ⟜-intro' to be opaque...
  ⟜-β' :
    ∀ (f : A ,, B ⊢ C) →
    _b∘r_ {B = C ⟜ A}{C = C} ⟜-app' (⟜-intro' f) ≡ f
  ⟜-β' f = refl

  ⟜-η' :
    ∀ (f : A ⊢ B ⟜ C) → f ≡ ⟜-intro' (_b∘r_ {B = B ⟜ C}{C = B} ⟜-app' f)
  ⟜-η' f = refl


⟜-intro-ε :
  A ⊢ C → ε ⊢ C ⟜ A
⟜-intro-ε f = ⟜-intro (f ∘g ⊗-unit-r)

⟜-intro⁻ :
  A ⊢ B ⟜ C →
  C ⊗ A ⊢ B
⟜-intro⁻ f = ⟜-app ∘g id ,⊗ f

opaque
  unfolding _⟜_ _⊗_ ⊗-intro ⊗≡
  ⟜-intro∘⟜-intro⁻≡id :
    (e : A ⊢ B ⟜ C) →
    ⟜-intro {A = C}{B = A}{C = B}(⟜-intro⁻ e) ≡ e
  ⟜-intro∘⟜-intro⁻≡id e = funExt λ w → funExt λ pA →
    funExt λ w' → funExt λ pB → transportRefl _

  ⟜-intro⁻∘⟜-intro≡id :
    (e : A ⊗ B ⊢ C) →
    ⟜-intro⁻ {A = B}{B = C}{C = A}(⟜-intro e) ≡ e
  ⟜-intro⁻∘⟜-intro≡id {C = C} e =
    funExt λ w → funExt λ p⊗ →
      fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
        (⊗PathP (≡-× refl refl) (≡-× refl refl)))

  -- THE ORDER SWAPS!
  ⟜-curry :
    A ⟜ (B ⊗ C) ⊢ (A ⟜ B) ⟜ C
  ⟜-curry {A = A} =
    ⟜-intro (⟜-intro {C = A}(⟜-app ∘g ⊗-assoc))

  ⟜-β :
    (m : (A ⊗ B) ⊢ C) →
    (⟜-intro⁻ (⟜-intro m))
      ≡
    m
  ⟜-β {C = C} m = funExt (λ w → funExt (λ p⊗ →
    fromPathP {A = λ i → C (p⊗ .fst .snd (~ i))}
      (congP (λ _ → m _) (⊗PathP refl refl))))

  ⟜-η :
    (f : A ⊢ B ⟜ C) →
    f
      ≡
    (⟜-intro (⟜-intro⁻ f))
  ⟜-η f = funExt (λ w → funExt (λ p⊗ → funExt (λ w' → funExt
    (λ q⊗ → sym (transportRefl (f _ p⊗ w' q⊗))))))

⟜UMP : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
  → Iso (A ⊗ B ⊢ C) (B ⊢ C ⟜ A)
⟜UMP {C = C} =
  iso ⟜-intro ⟜-intro⁻
    (λ b → sym (⟜-η b))
    ⟜-β

opaque
  unfolding _⊸_ _⊗_ ⊗-intro
  ⊸-intro :
    A ⊗ B ⊢  C →
    A ⊢ B ⊸ C
  ⊸-intro e _ p w' q =
    e _ ((_ , refl) , p , q)

  ⊸-app :
    (A ⊸ B) ⊗ A ⊢ B
  ⊸-app {B = B} _ (((w' , w'') , w≡w'++w'') , f , inp) =
    subst B (sym w≡w'++w'') (f _ inp)

  ⊸-intro' :
    A ,, B ⊢ C
    → A ⊢ B ⊸ C
  ⊸-intro' f w x w' x₁ = f w w' x x₁

  ⊸-app' :
    (A ⊸ B) ,, A ⊢ B
  ⊸-app' w w' fp Ap = fp w' Ap

  ⊸-β' :
    ∀ (f : A ,, B ⊢ C) →
    _b∘l_ {A = B ⊸ C}{C = C} ⊸-app' (⊸-intro' f) ≡ f
  ⊸-β' f = refl

  ⊸-η' :
    ∀ (f : A ⊢ C ⊸ B) →
    f ≡ ⊸-intro' (_b∘l_ {A = C ⊸ B}{C = B} ⊸-app' f)
  ⊸-η' f = refl

⊸-intro⁻ :
  A ⊢ B ⊸ C →
  A ⊗ B ⊢ C
⊸-intro⁻ {B = B}{C = C} f =
  ⊸-app ∘g ⊗-intro f (id {A = B})

opaque
  unfolding _⊸_ ⊸-intro ⊗≡
  ⊸-η :
    (e : A ⊢ B ⊸ C) →
    ⊸-intro (⊸-intro⁻ e) ≡ e
  ⊸-η e = funExt λ w → funExt λ pA →
    funExt λ w' → funExt λ pB → transportRefl _

  ⊸-β :
    (e : A ⊗ B ⊢ C) →
    ⊸-intro⁻ (⊸-intro e) ≡ e
  ⊸-β e = funExt λ w → funExt λ p⊗ →
    fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
      (⊗PathP refl refl))

-- THE ORDER SWAPS!
⊸-mapCod : C ⊢ D → A ⊸ C ⊢ A ⊸ D
⊸-mapCod f = ⊸-intro (f ∘g ⊸-app)

⟜-mapCod : C ⊢ D → C ⟜ A ⊢ D ⟜ A
⟜-mapCod f = ⟜-intro (f ∘g ⟜-app)

opaque
  unfolding ⊸-intro

  ⊸-mapCod-precomp : (e : A ⊢ B)(f : C ⊗ D ⊢ A) →
    ⊸-mapCod e ∘g ⊸-intro f ≡ ⊸-intro (e ∘g f)
  ⊸-mapCod-precomp {A = A}{B = B}{D = D} e f =
    funExt λ w → funExt λ p → funExt λ w' → funExt λ q →
    cong (e (w ++ w')) (transportRefl (⊸-intro {B = D} f w p w' q))

opaque
  unfolding ⊗-intro
  ⊸-mapCod-postcompε : (e : A ⊢ B)(f : ε ⊢ A) →
    (⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻) ∘g ⊸-mapCod e ≡
      e ∘g ⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻
  ⊸-mapCod-postcompε e f =
    cong ((⊸-app ∘g id ,⊗ f) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ (λ i → ⊸-β (e ∘g ⊸-app) i ∘g (id ,⊗ f) ∘g ⊗-unit-r⁻)

⊸-mapDom : A ⊢ B → B ⊸ C ⊢ A ⊸ C
⊸-mapDom f = ⊸-intro (⊸-app ∘g id ,⊗ f)

opaque
  -- why do we need to unfold ⊸-intro here?
  unfolding ⊸-intro
  ⊸-mapDom-precomp : (e : A ⊢ B)(f : C ⊗ B ⊢ B) →
    ⊸-mapDom e ∘g ⊸-intro f ≡ ⊸-intro (f ∘g id ,⊗ e)
  ⊸-mapDom-precomp {A = A}{B = B} e f =
      ⊸-η {C = B} (⊸-intro (f ∘g id ,⊗ e))

opaque
  unfolding ⊗-intro
  ⊸-mapDom-postcompε : (e : A ⊢ B)(f : ε ⊢ A) →
    (⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻) ∘g ⊸-mapDom {C = C} e ≡
      ⊸-app ∘g id ,⊗ (e ∘g f) ∘g ⊗-unit-r⁻
  ⊸-mapDom-postcompε e f =
    cong ((⊸-app ∘g id ,⊗ f) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ λ i → ⊸-β (⊸-app ∘g id ,⊗ e) i ∘g (id ,⊗ f) ∘g ⊗-unit-r⁻

⊸-curry :
  (A ⊗ B) ⊸ C ⊢ A ⊸ (B ⊸ C)
⊸-curry {C = C} = ⊸-intro (⊸-intro (⊸-app ∘g ⊗-assoc⁻))

⊸-intro-ε :
  A ⊢ C → ε ⊢ A ⊸ C
⊸-intro-ε f = ⊸-intro (f ∘g ⊗-unit-l)

⊸-intro-ε-β :
  (f : A ⊢ C)
  → ⊸-app ∘g (⊸-intro-ε f) ,⊗ id ≡ f ∘g ⊗-unit-l
⊸-intro-ε-β f = ⊸-β (f ∘g ⊗-unit-l)

⊸2-intro-ε :
  A1 ⊗ A2 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ C
⊸2-intro-ε {C = C} f = ⊸-curry ∘g ⊸-intro-ε f

⊸3-intro-ε :
  A1 ⊗ A2 ⊗ A3 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C
⊸3-intro-ε {C = C} f =
  ⊸-mapCod (⊸-curry {C = C})
  ∘g ⊸2-intro-ε f

⊸4-intro-ε :
  A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C
⊸4-intro-ε {C = C} f =
  ⊸-mapCod (⊸-mapCod (⊸-curry {C = C}))
  ∘g ⊸3-intro-ε f

⊸UMP : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
  → Iso (A ⊗ B ⊢ C) (A ⊢ B ⊸ C)
⊸UMP {B = B} = iso ⊸-intro ⊸-intro⁻ (⊸-η {B = B}) ⊸-β

-- applying a multi-argument function to the front of a substitution
⊸-app-l : (A ⊸ B) ⊗ A ⊗ D ⊢ B ⊗ D
⊸-app-l = (⊗-intro ⊸-app id ∘g ⊗-assoc)

⊸0⊗ : ε ⊢ C → D ⊢ C ⊗ D
⊸0⊗ f = f ,⊗ id ∘g ⊗-unit-l⁻

⊸1⊗ : ε ⊢ A1 ⊸ C → A1 ⊗ B ⊢ C ⊗ B
⊸1⊗ f = ⊸-app-l ∘g ⊸0⊗ f

⊸2⊗ : ε ⊢ A1 ⊸ A2 ⊸ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
⊸2⊗ f = ⊸-app-l ∘g ⊸1⊗ f

⊸2⊗' : A1 ⊗ A2 ⊢ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
⊸2⊗' f = f ,⊗ id ∘g ⊗-assoc

⊸3⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ D ⊢ C ⊗ D
⊸3⊗ f = ⊸-app-l ∘g ⊸2⊗ f

⊸4⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ D ⊢ C ⊗ D
⊸4⊗ f = ⊸-app-l ∘g ⊸3⊗ f

⟜0⊗ : ε ⊢ C → D ⊢ D ⊗ C
⟜0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻


opaque
  unfolding ⊗-intro
  ⊸-app⟜0⊗ :
    ∀ (f : A ⊗ B ⊢ C) (x : ε ⊢ B) →
    ⊸-app ∘g ⟜0⊗ x ∘g ⊸-intro f ≡ f ∘g ⟜0⊗ x
  ⊸-app⟜0⊗ f x =
    cong ((⊸-app ∘g id ,⊗ x) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ λ i → ⊸-β f i ∘g (id ,⊗ x) ∘g ⊗-unit-r⁻

⊸≡ : ∀ (f f' : A ⊢ C ⊸ B)
  → ⊸-app ∘g (f ,⊗ id) ≡ ⊸-app ∘g (f' ,⊗ id)
  → f ≡ f'
⊸≡ f f' p =
  sym (⊸-η f)
  ∙ cong ⊸-intro p
  ∙ ⊸-η f'

⟜≡ : ∀ (f f' : A ⊢ C ⟜ B)
  → ⟜-app ∘g (id ,⊗ f) ≡ ⟜-app ∘g (id ,⊗ f')
  → f ≡ f'
⟜≡ f f' p =
  ⟜-η f
  ∙ cong ⟜-intro p
  ∙ sym (⟜-η f')

opaque
  unfolding ⊗-intro
  ⊸-intro-natural :
    ⊸-intro f ∘g f' ≡ ⊸-intro (f ∘g f' ,⊗ id)
  ⊸-intro-natural {f = f}{f' = f'} = ⊸≡ _ _
    ((λ i → ⊸-β f i ∘g (f' ,⊗ id))
    ∙ sym (⊸-β _) )

  ⟜-intro-natural :
    ⟜-intro f ∘g f' ≡ ⟜-intro (f ∘g id ,⊗ f')
  ⟜-intro-natural {f = f}{f' = f'} =
    ⟜≡ _ _
      ((λ i → ⟜-β f i ∘g (id ,⊗ f'))
      ∙ sym (⟜-β _))

opaque
  unfolding _⊸_
  isSetGrammar⊸ : isSetGrammar A → isSetGrammar (B ⊸ A)
  isSetGrammar⊸ isSetA w = isSetΠ (λ w' → isSet→ (isSetA _))

opaque
  unfolding _⟜_
  isSetGrammar⟜ : isSetGrammar B → isSetGrammar (B ⟜ A)
  isSetGrammar⟜ isSetB w = isSetΠ (λ w' → isSet→ (isSetB _))

Element→Term : ↑ (A ⊸ B) → A ⊢ B
Element→Term f =
  ⊸-app
  ∘g ε-elim f ,⊗ id
  ∘g ⊗-unit-l⁻

Term→Element : A ⊢ B → ↑ (A ⊸ B)
Term→Element e = ⊸-intro (e ∘g ⊗-unit-l) [] ε-intro
