{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.MonoidalStructure.AsPath (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List.Base
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet as ⊗Path
import Grammar.Epsilon.AsPath.Base Alphabet isSetAlphabet as εPath
import Grammar.Literal.AsPath.Base Alphabet isSetAlphabet as LiteralPath
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A B C D : Grammar ℓA

open MonoidalStr

asPathMonoidalStr : MonoidalStr ℓA
asPathMonoidalStr .ε = εPath.ε*
asPathMonoidalStr .ε-intro = εPath.ε*-intro
asPathMonoidalStr .ε-elim = εPath.ε*-elim
asPathMonoidalStr .literal = LiteralPath.literal*
asPathMonoidalStr .lit-intro = LiteralPath.lit*-intro
asPathMonoidalStr ._⊗_ = ⊗Path._⊗_
asPathMonoidalStr .⊗-intro = ⊗Path.⊗-intro
asPathMonoidalStr .⊗-unit-r = ⊗Path.⊗-unit*-r
asPathMonoidalStr .⊗-unit-r⁻ = ⊗Path.⊗-unit*-r⁻
asPathMonoidalStr .⊗-unit-l = ⊗Path.⊗-unit*-l
asPathMonoidalStr .⊗-unit-l⁻ = ⊗Path.⊗-unit*-l⁻
asPathMonoidalStr .⊗-assoc = ⊗Path.⊗-assoc
asPathMonoidalStr .⊗-assoc⁻ = ⊗Path.⊗-assoc⁻
