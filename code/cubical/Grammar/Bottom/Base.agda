open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Function Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

opaque
  ⊥ : Grammar ℓ-zero
  ⊥ _ = Empty.⊥

  ⊥-elim :
    ⊥ ⊢ g
  ⊥-elim _ = Empty.elim

  ⊥-η : ∀ (f f' : ⊥ ⊢ g)
    → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt Empty.elim

  get⊥ : ∀ {w} → ⊥ w → Empty.⊥
  get⊥ p = p

⊥* : ∀ {ℓ : Level} → Grammar ℓ
⊥* {ℓ = ℓ} = LiftG ℓ ⊥

⊥*-elim :
  ⊥* {ℓg} ⊢ g
⊥*-elim = ⊥-elim ∘g lowerG
