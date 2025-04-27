open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.AsPath (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Epsilon.AsPath.Base Alphabet isSetAlphabet public
