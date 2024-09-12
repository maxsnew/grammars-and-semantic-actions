open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓ : Level
    g : Grammar ℓg

⊤ : Grammar ℓ-zero
⊤ _ = Unit

⊤* : Grammar ℓg
⊤* _ = Unit*

⊤-intro :
  g ⊢ ⊤
⊤-intro _ _ = tt

⊤*-intro : ∀ {ℓg} → g ⊢ ⊤* {ℓg}
⊤*-intro _ _ = tt*

unambiguous : Grammar ℓg → Typeω
unambiguous {ℓg = ℓg} g = is-mono {h = ⊤} (⊤-intro {g = g})
