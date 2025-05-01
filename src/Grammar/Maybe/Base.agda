{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

import Erased.Data.Maybe.Base as Maybe
import Erased.Data.Sum.Base as Sum

open import Grammar Alphabet isSetAlphabet hiding (k ; μ)
open import Term Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

Maybe : Grammar ℓA → Grammar ℓA
Maybe A = A ⊕ ⊤

just : A ⊢ Maybe A
just = inl

nothing : A ⊢ Maybe B
nothing = inr ∘g ⊤-intro

return : A ⊢ Maybe A
return = just

μMaybe : Maybe (Maybe A) ⊢ Maybe A
μMaybe = ⊕-elim id nothing

fmap :
  A ⊢ B →
  Maybe A ⊢ Maybe B
fmap e = ⊕-elim (just ∘g e) nothing

Maybe⊗l : (Maybe A) ⊗ B ⊢ Maybe (A ⊗ B)
Maybe⊗l {A = A}{B = B} =
  ⊸-intro⁻
    (⊕-elim
      (⊸-intro just)
      (⊸-intro (nothing {B = A ⊗ B})))

Maybe⊗r : A ⊗ (Maybe B)  ⊢ Maybe (A ⊗ B)
Maybe⊗r {A = A}{B = B} =
  ⟜-intro⁻
    (⊕-elim
       (⟜-intro just)
       (⟜-intro (nothing {B = A ⊗ B}))
    )

Maybe⊗ : (Maybe A) ⊗ (Maybe B) ⊢ Maybe (A ⊗ B)
Maybe⊗ {A = A}{B = B} =
  ⟜-intro⁻
    (⊕-elim
      (⟜-intro {C = Maybe (A ⊗ B)}
        (⊸-intro⁻
          (⊕-elim
            (⊸-intro just)
            (⊸-intro (nothing {B = A ⊗ B})))))
      (⟜-intro (nothing {B = A ⊗ B})))

opaque
  unfolding _⊕_
  extractMaybe : ∀ {w} → (Maybe A) w → Maybe.Maybe (A w)
  extractMaybe (Sum.inl a) = Maybe.just a
  extractMaybe (Sum.inr _) = Maybe.nothing
