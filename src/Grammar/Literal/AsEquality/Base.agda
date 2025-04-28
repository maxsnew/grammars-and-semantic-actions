{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsEquality.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure

open import Erased.Data.List
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet hiding (⟨_⟩)
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA
    c : Alphabet

opaque
  literal : Alphabet → Grammar ℓ-zero
  literal c w = w Eq.≡ [ c ]

  lit-intro : literal c [ c ]
  lit-intro = Eq.refl

  @0 isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w = isPropRetract Eq.eqToPath Eq.pathToEq
                        Eq.pathToEq-eqToPath (isSetString w [ c ])

＂_＂ : Alphabet → Grammar ℓ-zero
＂ c ＂ = literal c

@0 isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

-- This * here is a Cubical naming convention for
-- a lifted type, not a Kleene star
@0 literal* : ∀ {ℓ : Level} → Alphabet → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)
