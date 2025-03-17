open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automata.NFA (Alphabet : hSet ℓ-zero) where

open import Automata.NFA.Base Alphabet public
open import Automata.NFA.Properties Alphabet public
