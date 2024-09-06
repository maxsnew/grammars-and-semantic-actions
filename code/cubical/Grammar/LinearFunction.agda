open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.LinearFunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_⊸_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊸ h) w = ∀ (w' : String) → g w' → h (w' ++ w)

_⟜_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⟜ h) w = ∀ (w' : String) → h w' → g (w ++ w')

⊸-intro :
  g ⊗ h ⊢ k →
  h ⊢ g ⊸ k
⊸-intro e _ p w' q =
  e _ ((_ , refl) , (q , p))

⊸-app :
  g ⊗ (g ⊸ h) ⊢ h
⊸-app {h = h} _ p = subst h (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

⊸-intro⁻ :
  g ⊢ h ⊸ k →
  h ⊗ g ⊢ k
⊸-intro⁻ {h = h}{k = k} f =
  ⊸-app ∘g (⊗-intro (id {g = h}) f)

⊸-intro∘⊸-intro⁻≡id :
  (e : g ⊢ h ⊸ k) →
  ⊸-intro {g = h}{h = g}{k = k}(⊸-intro⁻ e) ≡ e
⊸-intro∘⊸-intro⁻≡id e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ ph → transportRefl _

⊸-intro⁻∘⊸-intro≡id :
  (e : g ⊗ h ⊢ k) →
  ⊸-intro⁻ {g = h}{h = g}{k = k}(⊸-intro e) ≡ e
⊸-intro⁻∘⊸-intro≡id {k = k} e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP (≡-× refl refl) (≡-× refl refl)))


-- TODO : this needs a better name
⊸-strength :
  (g ⊸ h) ⊗ k ⊢ g ⊸ (h ⊗ k)
⊸-strength {g = g}{h = h}{k = k} =
  ⊸-intro {g = g}{h = (g ⊸ h) ⊗ k}{k = h ⊗ k}
    (⊗-assoc ⋆ ⊗-intro ⊸-app id)

-- THE ORDER SWAPS!
⊸-curry :
  (g ⊗ h) ⊸ k ⊢ h ⊸ (g ⊸ k)
⊸-curry {g = g}{k = k} =
  ⊸-intro {k = g ⊸ k} (⊸-intro {k = k} (⊸-app ∘g ⊗-assoc))

⊸-β :
  (m : (g ⊗ h) ⊢ k) →
  (⊸-intro⁻ {g = h}{h = g}{k = k} (⊸-intro {g = g}{h = h}{k = k} m))
    ≡
  m
⊸-β {k = k} m = funExt (λ w → funExt (λ p⊗ →
  fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
    (congP (λ _ → m _) (⊗PathP refl refl))))

⊸-η :
  (f : g ⊢ h ⊸ k) →
  f
    ≡
  (⊸-intro {g = h}{h = g}{k = k} (⊸-intro⁻ {g = g}{h = h}{k = k} f))
⊸-η f = funExt (λ w → funExt (λ p⊗ → funExt (λ w' → funExt
  (λ q⊗ → sym (transportRefl (f _ p⊗ w' q⊗))))))


⟜-intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⟜ h
⟜-intro e _ p w' q =
  e _ ((_ , refl) , p , q)

⟜-app :
  (g ⟜ h) ⊗ h ⊢ g
⟜-app {g = g} _ (((w' , w'') , w≡w'++w'') , f , inp) =
  subst g (sym w≡w'++w'') (f _ inp)

⟜-intro⁻ :
  g ⊢ h ⟜ k →
  g ⊗ k ⊢ h
⟜-intro⁻ {h = h}{k = k} f =
  ⟜-app ∘g ⊗-intro f (id {g = k})

⟜-η :
  (e : g ⊢ h ⟜ k) →
  ⟜-intro {g = g}{h = k}{k = h}(⟜-intro⁻ e) ≡ e
⟜-η e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ pk → transportRefl _

⟜-β :
  (e : g ⊗ h ⊢ k) →
  ⟜-intro⁻ {g = g}{h = k}{k = h}(⟜-intro e) ≡ e
⟜-β e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP refl refl))

⟜-curry :
  g ⊗ (h ⟜ k) ⊢ (g ⊗ h) ⟜ k
⟜-curry {g = g}{h = h}{k = k} =
  ⟜-intro (⊗-intro id ⟜-app ∘g ⊗-assoc⁻)

⟜UMP : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
  → Iso (g ⊗ h ⊢ k) (g ⊢ k ⟜ h)
⟜UMP {k = k} = iso ⟜-intro ⟜-intro⁻ (⟜-η {h = k}) ⟜-β
