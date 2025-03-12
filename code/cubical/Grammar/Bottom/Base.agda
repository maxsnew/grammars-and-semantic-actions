open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

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

  ⊥-η : ∀ (f f' : ⊥ ⊢ A)
    → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt Empty.elim

  get⊥ : ∀ {w} → ⊥ w → Empty.⊥
  get⊥ p = p
