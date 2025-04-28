{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.Empty.Base as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.LinearFunction.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  ⊥ : Grammar ℓ-zero
  ⊥ _ = Empty.⊥

  @0 ⊥* : Grammar ℓA
  ⊥* _ = Empty.⊥*

  ⊥-elim :
    ⊥ ⊢ A
  ⊥-elim _ = Empty.elim

  @0 ⊥*-elim :
    ⊥* {ℓB} ⊢ A
  ⊥*-elim _ x = Empty.elim (lower x)

  @0 ⊥-η : ∀ (f f' : ⊥ ⊢ A)
    → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt Empty.elim

  get⊥ : ∀ {w} → ⊥ w → Empty.⊥
  get⊥ p = p

⊗⊥ : A ⊗ ⊥ ⊢ ⊥
⊗⊥ = ⟜-app ∘g id ,⊗ ⊥-elim

⊥⊗ : ⊥ ⊗ A ⊢ ⊥
⊥⊗ = ⊸-app ∘g ⊥-elim ,⊗ id
