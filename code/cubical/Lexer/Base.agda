open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Lexer.Base where

open import Cubical.Data.Maybe

open import Grammar.Base

module _
  (Alphabet Alphabet' : hSet ℓ-zero)
  where

  -- Very loose, and probably incorrect definition
  -- of a lexer as a translation between alphabets
  Lexer : Type ℓ-zero
  Lexer = String Alphabet → Maybe (String Alphabet')
