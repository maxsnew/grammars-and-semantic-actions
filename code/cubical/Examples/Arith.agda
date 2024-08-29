{- Some presentations of the Dyck grammar of balanced parentheses and hopefully some parsers? -}

module Examples.Arith where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

data Tok : Type where
  + * [ ] : Tok
  num : ℕ → Tok
  
