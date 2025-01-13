open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Epsilon.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.FinSet

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Term Alphabet
open import Helper

private
  variable
    ℓG ℓH ℓK : Level
    g : Grammar ℓG
    h : Grammar ℓH

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  unambiguousε : unambiguous ε
  unambiguousε = ans
    where
    opaque
      unfolding ε
      ans : unambiguous ε
      ans = EXTERNAL.isLang→unambiguous isFinSetAlphabet
        isLangε

  unambiguousε* : ∀ {ℓ} → unambiguous (ε* {ℓ})
  unambiguousε* {ℓ = ℓ} = ans
    where
    opaque
      unfolding ε
      ans : unambiguous (ε* {ℓ})
      ans = EXTERNAL.isLang→unambiguous isFinSetAlphabet
        λ w → isPropLift (isLangε w)

