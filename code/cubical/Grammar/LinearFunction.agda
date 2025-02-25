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
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    f f' f'' : g ⊢ h
    k : Grammar ℓk
    l : Grammar ℓl

opaque
  unfolding _⊗_
  _⟜_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  (g ⟜ h) w = ∀ (w' : String) → h w' → g (w' ++ w)

  _⊸_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  (g ⊸ h) w = ∀ (w' : String) → g w' → h (w ++ w')

  infixr 2 _⊸_
  infixl 2 _⟜_

  ⟜-intro :
    g ⊗ h ⊢ k →
    h ⊢ k ⟜ g
  ⟜-intro e _ p w' q =
    e _ ((_ , refl) , (q , p))

  ⟜-app :
    g ⊗ (h ⟜ g) ⊢ h
  ⟜-app {h = h} _ p = subst h (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

  ⟜-intro' :
    g ,, h ⊢ k →
    h ⊢ k ⟜ g
  ⟜-intro' f w' p w q = f w w' q p

  ⟜-app' :
    g ,, (h ⟜ g) ⊢ h
  ⟜-app' w1 w2 gp f = f w1 gp

--   -- this makes me think we don't want ⟜-app' and ⟜-intro' to be opaque...
  ⟜-β' :
    ∀ (f : g ,, h ⊢ k) →
    _b∘r_ {h = k ⟜ g}{k = k} ⟜-app' (⟜-intro' f) ≡ f
  ⟜-β' f = refl

  ⟜-η' :
    ∀ (f : g ⊢ h ⟜ k) → f ≡ ⟜-intro' (_b∘r_ {h = h ⟜ k}{k = h} ⟜-app' f)
  ⟜-η' f = refl


⟜-intro-ε :
  g ⊢ k → ε ⊢ k ⟜ g
⟜-intro-ε f = ⟜-intro (f ∘g ⊗-unit-r)

⟜-intro⁻ :
  g ⊢ h ⟜ k →
  k ⊗ g ⊢ h
⟜-intro⁻ f = ⟜-app ∘g id ,⊗ f

opaque
  unfolding _⟜_ _⊗_ ⊗-intro ⊗≡
  ⟜-intro∘⟜-intro⁻≡id :
    (e : g ⊢ h ⟜ k) →
    ⟜-intro {g = k}{h = g}{k = h}(⟜-intro⁻ e) ≡ e
  ⟜-intro∘⟜-intro⁻≡id e = funExt λ w → funExt λ pg →
    funExt λ w' → funExt λ ph → transportRefl _

  ⟜-intro⁻∘⟜-intro≡id :
    (e : g ⊗ h ⊢ k) →
    ⟜-intro⁻ {g = h}{h = k}{k = g}(⟜-intro e) ≡ e
  ⟜-intro⁻∘⟜-intro≡id {k = k} e =
    funExt λ w → funExt λ p⊗ →
      fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
        (⊗PathP (≡-× refl refl) (≡-× refl refl)))

  -- THE ORDER SWAPS!
  ⟜-curry :
    g ⟜ (h ⊗ k) ⊢ (g ⟜ h) ⟜ k
  ⟜-curry {g = g} =
    ⟜-intro (⟜-intro {k = g}(⟜-app ∘g ⊗-assoc))

  ⟜-β :
    (m : (g ⊗ h) ⊢ k) →
    (⟜-intro⁻ (⟜-intro m))
      ≡
    m
  ⟜-β {k = k} m = funExt (λ w → funExt (λ p⊗ →
    fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
      (congP (λ _ → m _) (⊗PathP refl refl))))

  ⟜-η :
    (f : g ⊢ h ⟜ k) →
    f
      ≡
    (⟜-intro (⟜-intro⁻ f))
  ⟜-η f = funExt (λ w → funExt (λ p⊗ → funExt (λ w' → funExt
    (λ q⊗ → sym (transportRefl (f _ p⊗ w' q⊗))))))

⟜UMP : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
  → Iso (g ⊗ h ⊢ k) (h ⊢ k ⟜ g)
⟜UMP {k = k} =
  iso ⟜-intro ⟜-intro⁻
    (λ b → sym (⟜-η b))
    ⟜-β

opaque
  unfolding _⊸_ _⊗_ ⊗-intro
  ⊸-intro :
    g ⊗ h ⊢  k →
    g ⊢ h ⊸ k
  ⊸-intro e _ p w' q =
    e _ ((_ , refl) , p , q)

  ⊸-app :
    (g ⊸ h) ⊗ g ⊢ h
  ⊸-app {h = h} _ (((w' , w'') , w≡w'++w'') , f , inp) =
    subst h (sym w≡w'++w'') (f _ inp)

  ⊸-intro' :
    g ,, h ⊢ k
    → g ⊢ h ⊸ k
  ⊸-intro' f w x w' x₁ = f w w' x x₁

  ⊸-app' :
    (g ⊸ h) ,, g ⊢ h
  ⊸-app' w w' fp gp = fp w' gp

  ⊸-β' :
    ∀ (f : g ,, h ⊢ k) →
    _b∘l_ {g = h ⊸ k}{k = k} ⊸-app' (⊸-intro' f) ≡ f
  ⊸-β' f = refl

  ⊸-η' :
    ∀ (f : g ⊢ k ⊸ h) →
    f ≡ ⊸-intro' (_b∘l_ {g = k ⊸ h}{k = h} ⊸-app' f)
  ⊸-η' f = refl

⊸-intro⁻ :
  g ⊢ h ⊸ k →
  g ⊗ h ⊢ k
⊸-intro⁻ {h = h}{k = k} f =
  ⊸-app ∘g ⊗-intro f (id {g = h})

opaque
  unfolding _⊸_ ⊸-intro ⊗≡
  ⊸-η :
    (e : g ⊢ h ⊸ k) →
    ⊸-intro (⊸-intro⁻ e) ≡ e
  ⊸-η e = funExt λ w → funExt λ pg →
    funExt λ w' → funExt λ ph → transportRefl _

  ⊸-β :
    (e : g ⊗ h ⊢ k) →
    ⊸-intro⁻ (⊸-intro e) ≡ e
  ⊸-β e = funExt λ w → funExt λ p⊗ →
    fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
      (⊗PathP refl refl))

-- THE ORDER SWAPS!
⊸-mapCod : k ⊢ l → g ⊸ k ⊢ g ⊸ l
⊸-mapCod f = ⊸-intro (f ∘g ⊸-app)

⟜-mapCod : k ⊢ l → k ⟜ g ⊢ l ⟜ g
⟜-mapCod f = ⟜-intro (f ∘g ⟜-app)

opaque
  unfolding ⊸-intro

  ⊸-mapCod-precomp : (e : g ⊢ h)(f : k ⊗ l ⊢ g) →
    ⊸-mapCod e ∘g ⊸-intro f ≡ ⊸-intro (e ∘g f)
  ⊸-mapCod-precomp {g = g}{h = h}{l = l} e f =
    funExt λ w → funExt λ p → funExt λ w' → funExt λ q →
    cong (e (w ++ w')) (transportRefl (⊸-intro {h = l} f w p w' q))

opaque
  unfolding ⊗-intro
  ⊸-mapCod-postcompε : (e : g ⊢ h)(f : ε ⊢ g) →
    (⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻) ∘g ⊸-mapCod e ≡
      e ∘g ⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻
  ⊸-mapCod-postcompε e f =
    cong ((⊸-app ∘g id ,⊗ f) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ (λ i → ⊸-β (e ∘g ⊸-app) i ∘g (id ,⊗ f) ∘g ⊗-unit-r⁻)

⊸-mapDom : g ⊢ h → h ⊸ k ⊢ g ⊸ k
⊸-mapDom f = ⊸-intro (⊸-app ∘g id ,⊗ f)

opaque
  -- why do we need to unfold ⊸-intro here?
  unfolding ⊸-intro
  ⊸-mapDom-precomp : (e : g ⊢ h)(f : k ⊗ h ⊢ h) →
    ⊸-mapDom e ∘g ⊸-intro f ≡ ⊸-intro (f ∘g id ,⊗ e)
  ⊸-mapDom-precomp {g = g}{h = h} e f =
      ⊸-η {k = h} (⊸-intro (f ∘g id ,⊗ e))

opaque
  unfolding ⊗-intro
  ⊸-mapDom-postcompε : (e : g ⊢ h)(f : ε ⊢ g) →
    (⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻) ∘g ⊸-mapDom {k = k} e ≡
      ⊸-app ∘g id ,⊗ (e ∘g f) ∘g ⊗-unit-r⁻
  ⊸-mapDom-postcompε e f =
    cong ((⊸-app ∘g id ,⊗ f) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ λ i → ⊸-β (⊸-app ∘g id ,⊗ e) i ∘g (id ,⊗ f) ∘g ⊗-unit-r⁻

⊸-curry :
  (g ⊗ h) ⊸ k ⊢ g ⊸ (h ⊸ k)
⊸-curry {k = k} = ⊸-intro (⊸-intro (⊸-app ∘g ⊗-assoc⁻))

⊸-intro-ε :
  g ⊢ k → ε ⊢ g ⊸ k
⊸-intro-ε f = ⊸-intro (f ∘g ⊗-unit-l)

⊸-intro-ε-β :
  (f : g ⊢ k)
  → ⊸-app ∘g (⊸-intro-ε f) ,⊗ id ≡ f ∘g ⊗-unit-l
⊸-intro-ε-β f = ⊸-β (f ∘g ⊗-unit-l)

⊸2-intro-ε :
  g1 ⊗ g2 ⊢ k → ε ⊢ g1 ⊸ g2 ⊸ k
⊸2-intro-ε {k = k} f = ⊸-curry ∘g ⊸-intro-ε f

⊸3-intro-ε :
  g1 ⊗ g2 ⊗ g3 ⊢ k → ε ⊢ g1 ⊸ g2 ⊸ g3 ⊸ k
⊸3-intro-ε {k = k} f =
  ⊸-mapCod (⊸-curry {k = k})
  ∘g ⊸2-intro-ε f

⊸4-intro-ε :
  g1 ⊗ g2 ⊗ g3 ⊗ g4 ⊢ k → ε ⊢ g1 ⊸ g2 ⊸ g3 ⊸ g4 ⊸ k
⊸4-intro-ε {k = k} f =
  ⊸-mapCod (⊸-mapCod (⊸-curry {k = k}))
  ∘g ⊸3-intro-ε f

⊸UMP : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
  → Iso (g ⊗ h ⊢ k) (g ⊢ h ⊸ k)
⊸UMP {h = h} = iso ⊸-intro ⊸-intro⁻ (⊸-η {h = h}) ⊸-β

-- applying a multi-argument function to the front of a substitution
⊸-app-l : (g ⊸ h) ⊗ g ⊗ l ⊢ h ⊗ l
⊸-app-l = (⊗-intro ⊸-app id ∘g ⊗-assoc)

⊸0⊗ : ε ⊢ k → l ⊢ k ⊗ l
⊸0⊗ f = f ,⊗ id ∘g ⊗-unit-l⁻

⊸1⊗ : ε ⊢ g1 ⊸ k → g1 ⊗ h ⊢ k ⊗ h
⊸1⊗ f = ⊸-app-l ∘g ⊸0⊗ f

⊸2⊗ : ε ⊢ g1 ⊸ g2 ⊸ k → g1 ⊗ g2 ⊗ l ⊢ k ⊗ l
⊸2⊗ f = ⊸-app-l ∘g ⊸1⊗ f

⊸2⊗' : g1 ⊗ g2 ⊢ k → g1 ⊗ g2 ⊗ l ⊢ k ⊗ l
⊸2⊗' f = f ,⊗ id ∘g ⊗-assoc

⊸3⊗ : ε ⊢ g1 ⊸ g2 ⊸ g3 ⊸ k → g1 ⊗ g2 ⊗ g3 ⊗ l ⊢ k ⊗ l
⊸3⊗ f = ⊸-app-l ∘g ⊸2⊗ f

⊸4⊗ : ε ⊢ g1 ⊸ g2 ⊸ g3 ⊸ g4 ⊸ k → g1 ⊗ g2 ⊗ g3 ⊗ g4 ⊗ l ⊢ k ⊗ l
⊸4⊗ f = ⊸-app-l ∘g ⊸3⊗ f

⟜0⊗ : ε ⊢ k → l ⊢ l ⊗ k
⟜0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻


opaque
  unfolding ⊗-intro
  ⊸-app⟜0⊗ :
    ∀ (f : g ⊗ h ⊢ k) (x : ε ⊢ h) →
    ⊸-app ∘g ⟜0⊗ x ∘g ⊸-intro f ≡ f ∘g ⟜0⊗ x
  ⊸-app⟜0⊗ f x =
    cong ((⊸-app ∘g id ,⊗ x) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ λ i → ⊸-β f i ∘g (id ,⊗ x) ∘g ⊗-unit-r⁻

⊸≡ : ∀ (f f' : g ⊢ k ⊸ h)
  → ⊸-app ∘g (f ,⊗ id) ≡ ⊸-app ∘g (f' ,⊗ id)
  → f ≡ f'
⊸≡ f f' p =
  sym (⊸-η f)
  ∙ cong ⊸-intro p
  ∙ ⊸-η f'

⟜≡ : ∀ (f f' : g ⊢ k ⟜ h)
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
  isSetGrammar⊸ : isSetGrammar g → isSetGrammar (h ⊸ g)
  isSetGrammar⊸ isSetG w = isSetΠ (λ w' → isSet→ (isSetG _))

opaque
  unfolding _⟜_
  isSetGrammar⟜ : isSetGrammar h → isSetGrammar (h ⟜ g)
  isSetGrammar⟜ isSetH w = isSetΠ (λ w' → isSet→ (isSetH _))

Element→Term : ↑ (g ⊸ h) → g ⊢ h
Element→Term f =
  ⊸-app
  ∘g ε-elim f ,⊗ id
  ∘g ⊗-unit-l⁻

Term→Element : g ⊢ h → ↑ (g ⊸ h)
Term→Element e = ⊸-intro (e ∘g ⊗-unit-l) [] ε-intro
