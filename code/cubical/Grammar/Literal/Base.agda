open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Term.Base Alphabet

private
  variable
    ℓG : Level
    g : Grammar ℓG
    c : ⟨ Alphabet ⟩

opaque
  literal : ⟨ Alphabet ⟩ → Grammar ℓ-zero
  literal c w = w ≡ [ c ]

  lit-intro : (literal c) [ c ]
  lit-intro = refl

  literal-elim : g [ c ] → literal c ⊢ g
  literal-elim {g = g} gc w w≡[c] =
    subst g (sym w≡[c]) gc

  isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w = isSetString w [ c ]

＂_＂ : ⟨ Alphabet ⟩ → Grammar ℓ-zero
＂ c ＂ = literal c

isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

literal* : ∀ {ℓ : Level} → ⟨ Alphabet ⟩ → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)
