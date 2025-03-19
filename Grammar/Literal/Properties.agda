open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Sum.Unambiguous Alphabet
open import Grammar.String.Properties Alphabet

module _ (c : ⟨ Alphabet ⟩) where
  unambiguous-literal : unambiguous ＂ c ＂
  unambiguous-literal = unambiguous⊕ᴰ (Alphabet .snd) unambiguous-char c
