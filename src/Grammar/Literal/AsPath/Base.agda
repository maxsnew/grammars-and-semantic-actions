{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels

module @0 Grammar.Literal.AsPath.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure

open import Erased.Data.List

open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet hiding (⟨_⟩)
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓ : Level
    A : Grammar ℓA
    c : Alphabet

opaque
  literal : Alphabet → Grammar ℓ-zero
  literal c w = w ≡ [ c ]

  lit-intro : literal c [ c ]
  lit-intro = refl

  isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w = isSetString w [ c ]

＂_＂ : Alphabet → Grammar ℓ-zero
＂ c ＂ = literal c

isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

-- This * here is a Cubical naming convention for
-- a lifted type, not a Kleene star
literal* : ∀ {ℓ : Level} → Alphabet → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)

isLangLiteral* : ∀ c → isLang (literal* {ℓ = ℓ} c)
isLangLiteral* c = isLangLift (isLangLiteral c)

opaque
  unfolding literal
  lit*-intro : literal* {ℓ = ℓ} c [ c ]
  lit*-intro = lift lit-intro
