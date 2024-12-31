{- Equalizers are "solutions" to equations between two terms. -}

{-
  These look a bit like dependent/refinement types because they can
  be defined in terms of Sigma and equality, but you can have them in
  linear language.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Equalizer (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List hiding (rec ; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    f f' f'' : g ⊢ h
    l : Grammar ℓl

module _ {g : Grammar ℓ}{h : Grammar ℓ'} (f f' : g ⊢ h) where
  opaque
    equalizer : Grammar (ℓ-max ℓ ℓ')
    equalizer w = Σ[ x ∈ g w ] f w x ≡ f' w x

    eq-π : equalizer ⊢ g
    eq-π = λ w z → z .fst

    eq-π-pf : f ∘g eq-π ≡ f' ∘g eq-π
    eq-π-pf i w x = x .snd i

  module _ (f'' : k ⊢ g) (p : f ∘g f'' ≡ f' ∘g f'') where
    opaque
      unfolding equalizer
      eq-intro : k ⊢ equalizer
      eq-intro w x .fst = f'' w x
      eq-intro w x .snd i = p i w x

      eq-β : eq-π ∘g eq-intro ≡ f''
      eq-β = refl

  module _ (f'' : k ⊢ equalizer) where
    opaque
      unfolding equalizer eq-intro
      eq-η : f'' ≡ eq-intro (eq-π ∘g f'') λ i → eq-π-pf i ∘g f''
      eq-η i = f''

  equalizer-section :
    ∀ (f'' : g ⊢ equalizer) →
    (eq-π ∘g f'' ≡ id)
    → f ≡ f'
  equalizer-section f'' p =
    cong (f ∘g_) (sym p)
    ∙ cong (_∘g f'') eq-π-pf
    ∙ cong (f' ∘g_) p

module _ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk} (f f' : g ⊢ h)(f'' : h ⊢ k) where
  equalizer-cong : equalizer f f' ⊢ equalizer (f'' ∘g f) (f'' ∘g f')
  equalizer-cong = eq-intro (f'' ∘g f) (f'' ∘g f') (eq-π f f') (cong (f'' ∘g_) (eq-π-pf f f'))

open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Dependent Alphabet

module _ {A : Type ℓ} (F : A → Functor A) (g : A → Grammar ℓg)
  (e e' : ∀ (a : A) → μ F a ⊢ g a)
  (pf : ∀ (a : A) →
    e  a ∘g roll ∘g map (F a) (λ a' → eq-π (e a') (e' a')) ≡
    e' a ∘g roll ∘g map (F a) (λ a' → eq-π (e a') (e' a'))) where

  equalizer-ind-alg : Algebra F λ a → equalizer (e a) (e' a)
  equalizer-ind-alg a =
    eq-intro (e a) (e' a)
      (roll ∘g map (F a) (λ a' → eq-π (e a') (e' a')))
      (pf a)

  equalizer-ind : ∀ (a : A) → e a ≡ e' a
  equalizer-ind = λ a →
    equalizer-section (e a) (e' a)
      (rec F equalizer-ind-alg a)
      (ind-id' F (compHomo F (initialAlgebra F) equalizer-ind-alg (initialAlgebra F)
        ((λ a' → eq-π (e a') (e' a')) ,
         λ a' → eq-π-is-homo a')
        (recHomo F equalizer-ind-alg)) a)
    where

    opaque
      unfolding eq-π eq-intro
      eq-π-is-homo :
        ∀ a →
        eq-π (e a) (e' a) ∘g equalizer-ind-alg a ≡
          roll ∘g map (F a) λ a' → eq-π (e a') (e' a')
      eq-π-is-homo a = refl

equalizer-ind-unit : (F : Functor Unit) {g : Grammar ℓg}
  {e e' : μ (λ _ → F) tt ⊢ g}
  → (e ∘g roll ∘g map F (λ _ → eq-π e e'))
    ≡ (e' ∘g roll ∘g map F (λ _ → eq-π e e'))
  → e ≡ e'
equalizer-ind-unit F {g = g} pf = equalizer-ind {A = Unit} (λ _ → F) (λ _ → g) _ _ (λ _ → pf) tt

open import Grammar.LinearFunction Alphabet
eq-π-pf-⟜-intro :
  (f f' : g ⊗ h ⊢ l) →
  f ∘g (eq-π (⟜-intro f) (⟜-intro f') ,⊗ id) ≡ f' ∘g eq-π (⟜-intro f) (⟜-intro f') ,⊗ id
eq-π-pf-⟜-intro f f' =
  isoFunInjective ⟜UMP _ _
    (⟜-intro (f ∘g eq-π (⟜-intro f) (⟜-intro f') ,⊗ id)
      ≡⟨ sym (⟜-intro-natural {f = f} {f' = eq-π (⟜-intro f) (⟜-intro f')}) ⟩
    ⟜-intro f ∘g eq-π (⟜-intro f) (⟜-intro f')
      ≡⟨ eq-π-pf (⟜-intro f) (⟜-intro f') ⟩
    ⟜-intro f' ∘g eq-π (⟜-intro f) (⟜-intro f')
      ≡⟨ ⟜-intro-natural {f = f'} {f' = eq-π (⟜-intro f) (⟜-intro f')} ⟩
     ⟜-intro (f' ∘g eq-π (⟜-intro f) (⟜-intro f') ,⊗ id)
     ∎)

module _ {A : Type ℓ}
    (tag : A → Type ℓ)
    (F : ∀ a → tag a → Functor A)
    where

  private
    F' : A → Functor A
    F' a = ⊕e (tag a) (F a)

  module _
    (g : A → Grammar ℓg)
    (h : Grammar ℓh)
    (e e' : ∀ (a : A) → μ (λ a → ⊕e (tag a) (F a)) a ⊗ h ⊢ g a)
    (pf : ∀ (a : A) (t : tag a) →
      e a
      ∘g (roll
          ∘g map (F' a)
            (λ a' → eq-π (⟜-intro (e a')) (⟜-intro (e' a')))
          ∘g ⊕ᴰ-in t) ,⊗ id ≡
      e' a
      ∘g (roll
          ∘g map (F' a)
            (λ a' → eq-π (⟜-intro (e a')) (⟜-intro (e' a')))
          ∘g ⊕ᴰ-in t) ,⊗ id)
    where
    equalizer-ind-⊗l : ∀ (a : A) → e a ≡ e' a
    equalizer-ind-⊗l a =
      isoFunInjective ⟜UMP _ _
        (equalizer-ind
          F'
          (λ a → g a ⟜ h)
          (λ a → ⟜-intro (e a))
          (λ a → ⟜-intro (e' a))
          (λ a →
            ⊕ᴰ≡ _ _ (λ t →
              isoInvInjective ⟜UMP _ _
                (
                (λ i →
                  ⟜-intro⁻
                    (⟜-intro-natural
                      {f = e a}
                      {f' =
                        roll
                        ∘g map (F' a)
                            (λ a' →
                              eq-π (⟜-intro (e a'))
                                   (⟜-intro (e' a')))
                        ∘g ⊕ᴰ-in t}
                      i)
                ) ∙
                ⟜-β _ ∙
                pf a t ∙
                sym (⟜-β _) ∙
                (λ i →
                  ⟜-intro⁻
                    (⟜-intro-natural
                      {f = e' a}
                      {f' =
                        roll
                        ∘g map (F' a)
                            (λ a' →
                              eq-π (⟜-intro (e a'))
                                   (⟜-intro (e' a')))
                        ∘g ⊕ᴰ-in t}
                      (~ i)))
                )
            ))
          a
          )
