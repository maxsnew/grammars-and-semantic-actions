open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Product Alphabet
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

  ⊥* : Grammar ℓg
  ⊥* _ = Empty.⊥*

  ⊥-elim :
    ⊥ ⊢ g
  ⊥-elim _ = Empty.elim

  ⊥*-elim :
    ⊥* {ℓg} ⊢ g
  ⊥*-elim _ x = Empty.elim (lower x)

  ⊥-η : ∀ (f f' : ⊥ ⊢ g)
    → f ≡ f'
  ⊥-η _ _ = funExt λ _ → funExt Empty.elim

