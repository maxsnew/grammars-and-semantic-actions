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
  ⊥ : Grammar ℓA
  ⊥ _ = Empty.⊥*

  ⊥-elim : ⊥ {ℓB} ⊢ A
  ⊥-elim _ x = Empty.elim (lower x)

  @0 ⊥-η : ∀ (f f' : ⊥ {ℓB} ⊢ A) → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt λ where ()

  get⊥ : ∀ {w} → ⊥ {ℓB} w → Empty.⊥
  get⊥ ()

module _ {{monStr : MonoidalStr ℓA}} where
  open MonoidalStr monStr
  ⊗⊥ : A ⊗ ⊥ ⊢ ⊥
  ⊗⊥ = ⟜-app ∘g id ,⊗ ⊥-elim

  ⊥⊗ : ⊥ ⊗ A ⊢ ⊥
  ⊥⊗ = ⊸-app ∘g ⊥-elim ,⊗ id
