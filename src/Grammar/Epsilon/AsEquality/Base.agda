{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.AsEquality.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List
open import Erased.Lift.Base
import Erased.Data.Equality as Eq
import Erased.Data.Empty as Empty

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓ : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  ε : Grammar ℓ-zero
  ε w = w Eq.≡ []

  ε-intro : ε⊢ ε
  ε-intro = Eq.refl

  ε-elim : ∀ {A : Grammar ℓA} → ε⊢ A → ε ⊢ A
  ε-elim {A = A} A[] w Eq.refl = A[]

ε* : ∀ {ℓ : Level} → Grammar ℓ
ε* {ℓ = ℓ} = LiftG ℓ ε

opaque
  unfolding ε
  ε*-intro : ε⊢ (ε* {ℓ = ℓ})
  ε*-intro = lift ε-intro

  ε*-elim : ∀ {A : Grammar ℓA} → ε⊢ A → (ε* {ℓ = ℓ}) ⊢ A
  ε*-elim A[] w (lift Eq.refl)= A[]
