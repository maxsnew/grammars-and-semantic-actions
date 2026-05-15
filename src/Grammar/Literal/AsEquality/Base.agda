open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

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
  literal c w = w Eq.≡ [ c ]

  lit-intro : literal c [ c ]
  lit-intro = Eq.refl

  isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w =
    isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString w [ c ])

＂_＂ : ⟨ Alphabet ⟩ → Grammar ℓ-zero
＂ c ＂ = literal c

isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

literal* : ∀ {ℓ : Level} → ⟨ Alphabet ⟩ → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)

opaque
  unfolding literal lit-intro isLangLiteral
  unfoldLiteralDefs : Unit
  unfoldLiteralDefs = tt
