open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Base (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet

private
  variable ℓG ℓG' : Level

data RegularExpression  : Type ℓ-zero where
  ε-Reg : RegularExpression
  ⊥-Reg : RegularExpression
  _⊗Reg_ : RegularExpression → RegularExpression → RegularExpression
  literalReg : ⟨ Alphabet ⟩ → RegularExpression
  _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
  KL*Reg : RegularExpression → RegularExpression

Regex = RegularExpression

RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero
RegularExpression→Grammar  ε-Reg = ε
RegularExpression→Grammar  ⊥-Reg = ⊥
RegularExpression→Grammar (g ⊗Reg g') =
  (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
RegularExpression→Grammar (literalReg c) = literal c
RegularExpression→Grammar (g ⊕Reg g') =
  RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

⟦_⟧r : RegularExpression → Grammar ℓ-zero
⟦_⟧r = RegularExpression→Grammar

＂_＂r : ⟨ Alphabet ⟩ → RegularExpression
＂ c ＂r = literalReg c
infix 30 ＂_＂r

_⊗r_ : RegularExpression → RegularExpression → RegularExpression
r ⊗r r' = r ⊗Reg r'
infixr 20 _⊗r_

_⊕r_ : RegularExpression → RegularExpression → RegularExpression
r ⊕r r' = r ⊕Reg r'
infixr 20 _⊕r_

_*r : RegularExpression → RegularExpression
r *r = KL*Reg r
infix 30 _*r

_+r : RegularExpression → RegularExpression
r +r = r ⊗r r *r
infix 30 _+r
