open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as ⊥

open import Grammar.Base Alphabet

private
  variable
    ℓG : Level

⊥-grammar : Grammar ℓ-zero
⊥-grammar _ = ⊥

⊥*-grammar : Grammar ℓG
⊥*-grammar _ = ⊥*
