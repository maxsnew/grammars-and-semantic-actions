open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as ⊥

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg : Level
    g : Grammar ℓg

⊥-grammar : Grammar ℓ-zero
⊥-grammar _ = ⊥

⊥*-grammar : Grammar ℓg
⊥*-grammar _ = ⊥*

⊥-elim :
  ⊥-grammar ⊢ g
⊥-elim _ = ⊥.elim

⊥-η : ∀ (f f' : ⊥-grammar ⊢ g)
  → f ≡ f'
⊥-η _ _ = funExt λ _ → funExt ⊥.elim
