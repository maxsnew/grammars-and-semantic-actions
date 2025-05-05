{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsEquality.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure

open import Erased.Data.List
open import Erased.Lift.Base
import Cubical.Data.Equality as Eq

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
  literal c w = w Eq.≡ [ c ]

  lit-intro : literal c [ c ]
  lit-intro = Eq.refl

＂_＂ : Alphabet → Grammar ℓ-zero
＂ c ＂ = literal c

-- This * here is a Cubical naming convention for
-- a lifted type, not a Kleene star
literal* : ∀ {ℓ : Level} → Alphabet → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)

opaque
  unfolding literal
  lit*-intro : literal* {ℓ = ℓ} c [ c ]
  lit*-intro = lift Eq.refl
