{- Equalizers are "solutions" to equations between two terms. -}

{-
  These look a bit like dependent/refinement types because they can
  be defined in terms of Sigma and equality, but you can have them in
  linear language.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module @0 Grammar.Equalizer.AsPath.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.LinearProduct.AsPath.Base Alphabet
open import Grammar.Epsilon.AsPath.Base Alphabet
open import Grammar.Inductive.AsPath.Indexed Alphabet hiding (k)
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearFunction.AsPath.Base Alphabet

open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _ {A : Grammar ℓA}{B : Grammar ℓB} (f f' : A ⊢ B) where
  opaque
    equalizer : Grammar (ℓ-max ℓA ℓB)
    equalizer w = Σ[ x ∈ A w ] f w x ≡ f' w x

    eq-π : equalizer ⊢ A
    eq-π = λ w z → z .fst

    eq-π-pf : f ∘g eq-π ≡ f' ∘g eq-π
    eq-π-pf i w x = x .snd i

  module _ (f'' : C ⊢ A) (p : f ∘g f'' ≡ f' ∘g f'') where
    opaque
      unfolding equalizer
      eq-intro : C ⊢ equalizer
      eq-intro w x .fst = f'' w x
      eq-intro w x .snd i = p i w x

      eq-β : eq-π ∘g eq-intro ≡ f''
      eq-β = refl

  module _ (f'' : C ⊢ equalizer) where
    opaque
      unfolding equalizer eq-intro
      eq-η : f'' ≡ eq-intro (eq-π ∘g f'') λ i → eq-π-pf i ∘g f''
      eq-η i = f''

  equalizer-section :
    ∀ (f'' : A ⊢ equalizer) →
    (eq-π ∘g f'' ≡ id)
    → f ≡ f'
  equalizer-section f'' p =
    cong (f ∘g_) (sym p)
    ∙ cong (_∘g f'') eq-π-pf
    ∙ cong (f' ∘g_) p

module _ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} (f f' : A ⊢ B)(f'' : B ⊢ C) where
  equalizer-cong : equalizer f f' ⊢ equalizer (f'' ∘g f) (f'' ∘g f')
  equalizer-cong =
    eq-intro (f'' ∘g f) (f'' ∘g f')
      (eq-π f f') (cong (f'' ∘g_) (eq-π-pf f f'))

module _ {X : Type ℓX} (F : X → Functor X) (A : X → Grammar ℓA)
  (e e' : ∀ (x : X) → μ F x ⊢ A x)
  (pf : ∀ (x : X) →
    e  x ∘g roll ∘g map (F x) (λ x' → eq-π (e x') (e' x')) ≡
    e' x ∘g roll ∘g map (F x) (λ x' → eq-π (e x') (e' x'))) where

  equalizer-ind-alg : Algebra F λ x → equalizer (e x) (e' x)
  equalizer-ind-alg x =
    eq-intro (e x) (e' x)
      (roll ∘g map (F x) (λ x' → eq-π (e x') (e' x')))
      (pf x)

  equalizer-ind : ∀ (x : X) → e x ≡ e' x
  equalizer-ind = λ x →
    equalizer-section (e x) (e' x)
      (rec F equalizer-ind-alg x)
      (ind-id' F (compHomo F (initialAlgebra F) equalizer-ind-alg (initialAlgebra F)
        ((λ x' → eq-π (e x') (e' x')) ,
         λ x' → eq-π-is-homo x')
        (recHomo F equalizer-ind-alg)) x)
    where

    opaque
      unfolding eq-π eq-intro
      eq-π-is-homo :
        ∀ x →
        eq-π (e x) (e' x) ∘g equalizer-ind-alg x ≡
          roll ∘g map (F x) λ x' → eq-π (e x') (e' x')
      eq-π-is-homo x = refl

equalizer-ind-unit : (F : Functor Unit) {A : Grammar ℓA}
  {e e' : μ (λ _ → F) tt ⊢ A}
  → (e ∘g roll ∘g map F (λ _ → eq-π e e'))
    ≡ (e' ∘g roll ∘g map F (λ _ → eq-π e e'))
  → e ≡ e'
equalizer-ind-unit F {A = A} pf = equalizer-ind {X = Unit} (λ _ → F) (λ _ → A) _ _ (λ _ → pf) tt

eq-π-pf-⊸-intro :
  (f f' : A ⊗ B ⊢ C) →
  f ∘g (eq-π (⊸-intro f) (⊸-intro f') ,⊗ id) ≡ f' ∘g eq-π (⊸-intro f) (⊸-intro f') ,⊗ id
eq-π-pf-⊸-intro f f' =
  isoFunInjective ⊸UMP _ _
    (⊸-intro (f ∘g eq-π (⊸-intro f) (⊸-intro f') ,⊗ id)
      ≡⟨ sym (⊸-intro-natural {f = f} {f' = eq-π (⊸-intro f) (⊸-intro f')}) ⟩
    ⊸-intro f ∘g eq-π (⊸-intro f) (⊸-intro f')
      ≡⟨ eq-π-pf (⊸-intro f) (⊸-intro f') ⟩
    ⊸-intro f' ∘g eq-π (⊸-intro f) (⊸-intro f')
      ≡⟨ ⊸-intro-natural {f = f'} {f' = eq-π (⊸-intro f) (⊸-intro f')} ⟩
     ⊸-intro (f' ∘g eq-π (⊸-intro f) (⊸-intro f') ,⊗ id)
     ∎)

eq-π-pf-⟜-intro :
  (f f' : A ⊗ B ⊢ C) →
  f ∘g id ,⊗ eq-π (⟜-intro f) (⟜-intro f') ≡ f' ∘g id ,⊗ eq-π (⟜-intro f) (⟜-intro f')
eq-π-pf-⟜-intro f f' =
  isoFunInjective ⟜UMP _ _
    (⟜-intro (f ∘g id ,⊗ eq-π (⟜-intro f) (⟜-intro f'))
      ≡⟨ sym (⟜-intro-natural {f = f} {f' = eq-π (⟜-intro f) (⟜-intro f')}) ⟩
    ⟜-intro f ∘g eq-π (⟜-intro f) (⟜-intro f')
      ≡⟨ eq-π-pf (⟜-intro f) (⟜-intro f') ⟩
    ⟜-intro f' ∘g eq-π (⟜-intro f) (⟜-intro f')
      ≡⟨ ⟜-intro-natural {f = f'} {f' = eq-π (⟜-intro f) (⟜-intro f')} ⟩
     ⟜-intro (f' ∘g id ,⊗ eq-π (⟜-intro f) (⟜-intro f'))
     ∎)

module _ {X : Type ℓX}
    (tag : X → Type ℓX)
    (F : ∀ x → tag x → Functor X)
    where

  private
    F' : X → Functor X
    F' x = ⊕e (tag x) (F x)

  module _
    (A : X → Grammar ℓA)
    (B : X → Grammar ℓB)
    (e e' : ∀ (x : X) → μ (λ x → ⊕e (tag x) (F x)) x ⊗ B x ⊢ A x)
    (pf : ∀ (x : X) (t : tag x) →
      e x
      ∘g (roll
          ∘g map (F' x)
            (λ x' → eq-π (⊸-intro (e x')) (⊸-intro (e' x')))
          ∘g σ t) ,⊗ id ≡
      e' x
      ∘g (roll
          ∘g map (F' x)
            (λ x' → eq-π (⊸-intro (e x')) (⊸-intro (e' x')))
          ∘g σ t) ,⊗ id)
    where
    equalizer-ind-⊗l : ∀ (x : X) → e x ≡ e' x
    equalizer-ind-⊗l x =
      isoFunInjective ⊸UMP _ _
        (equalizer-ind
          F'
          (λ x → B x ⊸ A x)
          (λ x → ⊸-intro (e x))
          (λ x → ⊸-intro (e' x))
          (λ x →
            ⊕ᴰ≡ _ _ (λ t →
              isoInvInjective ⊸UMP _ _
                (
                (λ i →
                  ⊸-intro⁻
                    (⊸-intro-natural
                      {f = e x}
                      {f' =
                        roll
                        ∘g map (F' x)
                            (λ x' →
                              eq-π (⊸-intro (e x'))
                                   (⊸-intro (e' x')))
                        ∘g σ t}
                      i)
                ) ∙
                ⊸-β _ ∙
                pf x t ∙
                sym (⊸-β _) ∙
                (λ i →
                  ⊸-intro⁻
                    (⊸-intro-natural
                      {f = e' x}
                      {f' =
                        roll
                        ∘g map (F' x)
                            (λ x' →
                              eq-π (⊸-intro (e x'))
                                   (⊸-intro (e' x')))
                        ∘g σ t}
                      (~ i)))
                )
            ))
          x
          )

  module _
    (A : X → Grammar ℓA)
    (B : X → Grammar ℓB)
    (e e' : ∀ (x : X) → B x ⊗ μ (λ x → ⊕e (tag x) (F x)) x ⊢ A x)
    (pf : ∀ (x : X) (t : tag x) →
      e x
      ∘g id ,⊗ (roll
          ∘g map (F' x)
            (λ x' → eq-π (⟜-intro (e x')) (⟜-intro (e' x')))
          ∘g σ t) ≡
      e' x
      ∘g id ,⊗ (roll
          ∘g map (F' x)
            (λ x' → eq-π (⟜-intro (e x')) (⟜-intro (e' x')))
          ∘g σ t))
    where
    equalizer-ind-⊗r : ∀ (x : X) → e x ≡ e' x
    equalizer-ind-⊗r x =
      isoFunInjective ⟜UMP _ _
        (equalizer-ind
          F'
          (λ x → A x ⟜ B x)
          (λ x → ⟜-intro (e x))
          (λ x → ⟜-intro (e' x))
          (λ x →
            ⊕ᴰ≡ _ _ (λ t →
              isoInvInjective ⟜UMP _ _
                (
                (λ i →
                  ⟜-intro⁻
                    (⟜-intro-natural
                      {f = e x}
                      {f' =
                        roll
                        ∘g map (F' x)
                            (λ x' →
                              eq-π (⟜-intro (e x'))
                                   (⟜-intro (e' x')))
                        ∘g σ t}
                      i)
                ) ∙
                ⟜-β _ ∙
                pf x t ∙
                sym (⟜-β _) ∙
                (λ i →
                  ⟜-intro⁻
                    (⟜-intro-natural
                      {f = e' x}
                      {f' =
                        roll
                        ∘g map (F' x)
                            (λ x' →
                              eq-π (⟜-intro (e x'))
                                   (⟜-intro (e' x')))
                        ∘g σ t}
                      (~ i)))
                )
            )
            )
          x
          )
