open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsPath.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Term.Base Alphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA
    c : ⟨ Alphabet ⟩

opaque
  literal : ⟨ Alphabet ⟩ → Grammar ℓ-zero
  literal c w = w ≡ [ c ]

  @0 isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w = isSetString w [ c ]

＂_＂ : ⟨ Alphabet ⟩ → Grammar ℓ-zero
＂ c ＂ = literal c

@0 isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

-- This * here is a Cubical naming convention for
-- a lifted type, not a Kleene star
literal* : ∀ {ℓ : Level} → ⟨ Alphabet ⟩ → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)
