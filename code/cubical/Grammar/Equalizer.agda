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

open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Dependent Alphabet

module _ {A : Type ℓ} (F : A → Functor A) {g : Grammar ℓg}
  (e e' : ∀ (a : A) → μ F a ⊢ g) where
  equalizer-ind :
    (pf : ∀ (a : A) →
      e  a ∘g roll ∘g map (F a) (λ a' → eq-π (e a') (e' a')) ≡
      e' a ∘g roll ∘g map (F a) (λ a' → eq-π (e a') (e' a'))
    ) →
    ∀ (a : A) → e a ≡ e' a
  equalizer-ind pf = λ a →
    equalizer-section (e a) (e' a)
      (rec F pfAlg a)
      (ind-id' F (compHomo F (initialAlgebra F) pfAlg (initialAlgebra F)
        ((λ a' → eq-π (e a') (e' a')) ,
         λ a' → eq-π-is-homo a')
        (recHomo F pfAlg)) a)
    where
    pfAlg : Algebra F λ a → equalizer (e a) (e' a)
    pfAlg a =
      eq-intro (e a) (e' a)
        (roll ∘g map (F a) (λ a' → eq-π (e a') (e' a')))
        (pf a)

    opaque
      unfolding eq-π eq-intro
      eq-π-is-homo :
        ∀ a →
        eq-π (e a) (e' a) ∘g pfAlg a ≡
          roll ∘g map (F a) λ a' → eq-π (e a') (e' a')
      eq-π-is-homo a = refl
