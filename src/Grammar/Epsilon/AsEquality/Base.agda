open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB : Level
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
  ε*-intro : ε⊢ (ε* {ℓ-zero})
  ε*-intro = lift ε-intro

  ε*-elim : ∀ {ℓ} {A : Grammar ℓA} → ε⊢ A → (ε* {ℓ}) ⊢ A
  ε*-elim A[] w (lift Eq.refl) = A[]
