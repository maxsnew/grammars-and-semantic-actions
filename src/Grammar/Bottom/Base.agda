{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lower ; lift)
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.Empty.Base as Empty hiding (⊥ ; ⊥*)
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
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

  ⊥* : Grammar ℓA
  ⊥* _ = Empty.⊥*

  ⊥-elim :
    ⊥ ⊢ A
  ⊥-elim _ = Empty.elim

  ⊥*-elim :
    ⊥* {ℓB} ⊢ A
  ⊥*-elim _ x = Empty.elim (lower x)

  @0 ⊥-η : ∀ (f f' : ⊥ ⊢ A)
    → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt Empty.elim

  get⊥ : ∀ {w} → ⊥ w → Empty.⊥
  get⊥ p = p

module _ {{monStr : MonoidalStr}} where
  open MonoidalStr monStr
  ⊗⊥ : A ⊗ ⊥ ⊢ ⊥
  ⊗⊥ = ⟜-app ∘g id ,⊗ ⊥-elim

  ⊥⊗ : ⊥ ⊗ A ⊢ ⊥
  ⊥⊗ = ⊸-app ∘g ⊥-elim ,⊗ id
