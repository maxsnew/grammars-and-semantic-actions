open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automata.Turing (Alphabet : hSet ℓ-zero) where

open import Automata.Turing.OneSided.Base Alphabet public
