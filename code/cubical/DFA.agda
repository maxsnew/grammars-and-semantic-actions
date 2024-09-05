open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA (Alphabet : hSet ℓ-zero) where

open import DFA.Base Alphabet public
open import DFA.Decider Alphabet public
