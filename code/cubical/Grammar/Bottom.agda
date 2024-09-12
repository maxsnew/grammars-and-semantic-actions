open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg : Level
    g : Grammar ℓg

⊥ : Grammar ℓ-zero
⊥ _ = Empty.⊥

⊥* : Grammar ℓg
⊥* _ = Empty.⊥*

⊥-elim :
  ⊥ ⊢ g
⊥-elim _ = Empty.elim

⊥*-elim :
  ⊥ ⊢ g
⊥*-elim _ = Empty.elim

⊥-η : ∀ (f f' : ⊥ ⊢ g)
  → f ≡ f'
⊥-η _ _ = funExt λ _ → funExt Empty.elim
