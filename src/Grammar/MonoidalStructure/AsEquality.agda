{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.MonoidalStructure.AsEquality (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List.Base
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet as ⊗Eq
import Grammar.Epsilon.AsEquality.Base Alphabet isSetAlphabet as εEq
import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet as LiteralEq
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A B C D : Grammar ℓA

open MonoidalStr

asEqualityMonoidalStr : MonoidalStr ℓA
asEqualityMonoidalStr .ε = εEq.ε*
asEqualityMonoidalStr .ε-intro = εEq.ε*-intro
asEqualityMonoidalStr .ε-elim = εEq.ε*-elim
asEqualityMonoidalStr .literal = LiteralEq.literal*
asEqualityMonoidalStr .lit-intro = LiteralEq.lit*-intro
asEqualityMonoidalStr ._⊗_ = ⊗Eq._⊗_
asEqualityMonoidalStr .⊗-intro = ⊗Eq.⊗-intro
asEqualityMonoidalStr .⊗-unit-r = ⊗Eq.⊗-unit*-r
asEqualityMonoidalStr .⊗-unit-r⁻ = ⊗Eq.⊗-unit*-r⁻
asEqualityMonoidalStr .⊗-unit-l = ⊗Eq.⊗-unit*-l
asEqualityMonoidalStr .⊗-unit-l⁻ = ⊗Eq.⊗-unit*-l⁻
asEqualityMonoidalStr .⊗-assoc = ⊗Eq.⊗-assoc
asEqualityMonoidalStr .⊗-assoc⁻ = ⊗Eq.⊗-assoc⁻
