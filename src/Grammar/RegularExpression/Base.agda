open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Base (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.KleeneStar.Inductive Alphabet

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

infixr 25 _⊗r_

infixr 18 _⊕r_

infix 40 _*r

private
  test : ∀ (r1 r2 r3 : Grammar ℓ-zero)
    → r1 ⊕ r2 ⊗ r3 * ≡ r1 ⊕ (r2 ⊗ (r3 *))
  test _ _ _ = refl

  test2 : ∀ r1 r2 r3
    → r1 ⊕r r2 ⊗r r3 *r ≡ r1 ⊕r (r2 ⊗r (r3 *r))
  test2 _ _ _ = refl

_+r : RegularExpression → RegularExpression
r +r = r ⊗r r *r
infix 30 _+r
