open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

private
  variable
    ℓG : Level
    g : Grammar ℓG
    c : ⟨ Alphabet ⟩

opaque
  literal : ⟨ Alphabet ⟩ → Grammar ℓ-zero
  literal c w = w ≡ [ c ]

  literal-elim : g [ c ] → literal c ⊢ g
  literal-elim {g = g} gc w w≡[c] =
    subst g (sym w≡[c]) gc

literal* : ∀ {ℓ : Level} → ⟨ Alphabet ⟩ → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)
