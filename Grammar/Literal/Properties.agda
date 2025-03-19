open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.HLevels.Properties Alphabet
open import Term.Base Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  unambiguous-literal : unambiguous ＂ c ＂
  unambiguous-literal = ?
