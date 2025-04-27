open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

module @0 Grammar.LinearFunction.AsPath.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.LinearProduct.AsPath Alphabet
open import Grammar.LinearFunction.AsPath.Base Alphabet
open import Grammar.Epsilon.AsPath.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE : Level
    A A1 : Grammar ℓA
    B A2 : Grammar ℓB
    C A3 : Grammar ℓC
    D A4 : Grammar ℓD
    E A5 : Grammar ℓE
    f f' f'' : A ⊢ B

opaque
  unfolding _⟜_ ⊗PathP
  ⟜-β : (e : (A ⊗ B) ⊢ C) → ⟜-intro⁻ (⟜-intro e) ≡ e
  ⟜-β {C = C} e =
    funExt λ w → funExt λ where
      (s , a , b) → fromPathP {A = λ i → C (w≡l++r s (~ i))}
                      (congP (λ _ → e _) (⊗PathP refl refl))

  ⟜-η : (f : A ⊢ B ⟜ C) → f ≡ ⟜-intro (⟜-intro⁻ f)
  ⟜-η f = funExt (λ w → funExt (λ a → funExt (λ w' → funExt
    (λ c → sym (transportRefl (f _ a w' c))))))

⟜UMP : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
  → Iso (A ⊗ B ⊢ C) (B ⊢ C ⟜ A)
⟜UMP {C = C} = iso ⟜-intro ⟜-intro⁻ (λ b → sym (⟜-η b)) ⟜-β

opaque
  unfolding _⊸_ ⊸-intro ⊗PathP
  ⊸-η : (e : A ⊢ B ⊸ C) → ⊸-intro (⊸-intro⁻ e) ≡ e
  ⊸-η e = funExt λ _ → funExt λ a →
    funExt λ _ → funExt λ b → transportRefl _

  ⊸-β : (e : A ⊗ B ⊢ C) → ⊸-intro⁻ (⊸-intro e) ≡ e
  ⊸-β e = funExt λ w → funExt λ where
    (s , a , b) → fromPathP (congP₂ (λ _ → e) (sym (w≡l++r s)) (⊗PathP refl refl))

opaque
  unfolding ⊸-intro
  ⊸-mapCod-precomp : (e : A ⊢ B)(f : C ⊗ D ⊢ A) →
    ⊸-mapCod e ∘g ⊸-intro f ≡ ⊸-intro (e ∘g f)
  ⊸-mapCod-precomp {A = A}{B = B}{D = D} e f =
    funExt λ w → funExt λ c → funExt λ w' → funExt λ d →
    cong (e (w ++ w')) (transportRefl (⊸-intro {B = D} f w c w' d))

opaque
  unfolding ⊗-intro
  ⊸-mapCod-postcompε : (e : A ⊢ B)(f : ε ⊢ A) →
    (⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻) ∘g ⊸-mapCod e ≡ e ∘g ⊸-app ∘g id ,⊗ f ∘g ⊗-unit-r⁻
  ⊸-mapCod-postcompε e f =
    cong ((⊸-app ∘g id ,⊗ f) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ (λ i → ⊸-β (e ∘g ⊸-app) i ∘g (id ,⊗ f) ∘g ⊗-unit-r⁻)

opaque
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

⊸-intro-ε-β : (f : A ⊢ C) → ⊸-app ∘g (⊸-intro-ε f) ,⊗ id ≡ f ∘g ⊗-unit-l
⊸-intro-ε-β f = ⊸-β (f ∘g ⊗-unit-l)

⊸UMP : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
  → Iso (A ⊗ B ⊢ C) (A ⊢ B ⊸ C)
⊸UMP {B = B} = iso ⊸-intro ⊸-intro⁻ (⊸-η {B = B}) ⊸-β

opaque
  unfolding ⊗-intro
  ⊸-app⟜0⊗ : ∀ (f : A ⊗ B ⊢ C) (x : ε ⊢ B) → ⊸-app ∘g ⟜0⊗ x ∘g ⊸-intro f ≡ f ∘g ⟜0⊗ x
  ⊸-app⟜0⊗ f x =
    cong ((⊸-app ∘g id ,⊗ x) ∘g_) ⊗-unit-r⁻⊗-intro
    ∙ λ i → ⊸-β f i ∘g (id ,⊗ x) ∘g ⊗-unit-r⁻

⊸≡ : ∀ (f f' : A ⊢ C ⊸ B) → ⊸-app ∘g (f ,⊗ id) ≡ ⊸-app ∘g (f' ,⊗ id) → f ≡ f'
⊸≡ f f' p = sym (⊸-η f) ∙ cong ⊸-intro p ∙ ⊸-η f'

⟜≡ : ∀ (f f' : A ⊢ C ⟜ B) → ⟜-app ∘g (id ,⊗ f) ≡ ⟜-app ∘g (id ,⊗ f') → f ≡ f'
⟜≡ f f' p = ⟜-η f ∙ cong ⟜-intro p ∙ sym (⟜-η f')

opaque
  unfolding ⊗-intro
  ⊸-intro-natural : ⊸-intro f ∘g f' ≡ ⊸-intro (f ∘g f' ,⊗ id)
  ⊸-intro-natural {f = f}{f' = f'} = ⊸≡ _ _
    ((λ i → ⊸-β f i ∘g (f' ,⊗ id))
    ∙ sym (⊸-β _) )

  ⟜-intro-natural : ⟜-intro f ∘g f' ≡ ⟜-intro (f ∘g id ,⊗ f')
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

opaque
  unfolding ε-elim
  Term≅Element : Iso (A ⊢ B) (↑ (A ⊸ B))
  Term≅Element {A = A} {B = B} =
    iso Term→Element Element→Term
      (λ b →
        cong (λ z → ⊸-intro (⊸-app ∘g (ε-elim b) ,⊗ id ∘g z) [] ε-intro) ⊗-unit-ll⁻
        ∙ cong (λ z → z [] ε-intro) (⊸-η (ε-elim b))
        ∙ ε-β {A = A ⊸ B} b
      )
      (λ e →
        ⊸-app ∘g ε-elim (⊸-intro (e ∘g ⊗-unit-l) ∘ε ε-intro) ,⊗ id ∘g ⊗-unit-l⁻
          ≡⟨ cong (λ z → ⊸-app ∘g z ,⊗ id ∘g ⊗-unit-l⁻)
              (sym (ε-elim-natural ε-intro (⊸-intro (e ∘g ⊗-unit-l))))⟩
        ⊸-app ∘g (⊸-intro (e ∘g ⊗-unit-l) ∘g ε-elim ε-intro) ,⊗ id ∘g ⊗-unit-l⁻
          ≡⟨ cong (λ z → ⊸-app ∘g (⊸-intro (e ∘g ⊗-unit-l) ∘g z) ,⊗ id ∘g ⊗-unit-l⁻)
               (funExt λ w → funExt λ p → isSetString w [] (ε-elim {A = ε} ε-intro w p) p)⟩
        ⊸-app ∘g (⊸-intro (e ∘g ⊗-unit-l)) ,⊗ id ∘g ⊗-unit-l⁻
          ≡⟨ cong (_∘g ⊗-unit-l⁻) (⊸-β (e ∘g ⊗-unit-l)) ⟩
        e ∘g ⊗-unit-l ∘g ⊗-unit-l⁻
          ≡⟨ cong (e ∘g_) ⊗-unit-l⁻l ⟩
        e
        ∎)
