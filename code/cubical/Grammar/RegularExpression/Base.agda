open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Base (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet

data RegularExpression  : Type ℓ-zero where
  εr : RegularExpression
  ⊥r : RegularExpression
  _⊗r_ : RegularExpression → RegularExpression → RegularExpression
  ＂_＂r : ⟨ Alphabet ⟩ → RegularExpression
  _⊕r_ : RegularExpression → RegularExpression → RegularExpression
  _*r : RegularExpression → RegularExpression

Regex = RegularExpression

RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero
RegularExpression→Grammar  εr = ε
RegularExpression→Grammar  ⊥r = ⊥
RegularExpression→Grammar (r ⊗r r') =
  (RegularExpression→Grammar r) ⊗ (RegularExpression→Grammar r')
RegularExpression→Grammar (＂ c ＂r) = literal c
RegularExpression→Grammar (r ⊕r r') =
  RegularExpression→Grammar r ⊕ RegularExpression→Grammar r'
RegularExpression→Grammar (r *r) = (RegularExpression→Grammar r) *

⟦_⟧r : RegularExpression → Grammar ℓ-zero
⟦_⟧r = RegularExpression→Grammar

infix 30 ＂_＂r

infixr 20 _⊗r_

infixr 20 _⊕r_

infix 30 _*r

_+r : RegularExpression → RegularExpression
r +r = r ⊗r r *r
infix 30 _+r
