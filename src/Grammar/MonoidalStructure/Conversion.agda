{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.MonoidalStructure.Conversion (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List.Base
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.AsEquality Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.AsPath Alphabet isSetAlphabet
import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet as ⊗Path
import Grammar.Epsilon.AsPath.Base Alphabet isSetAlphabet as εPath
import Grammar.Literal.AsPath.Base Alphabet isSetAlphabet as LiteralPath
import Grammar.LinearProduct.AsEquality Alphabet isSetAlphabet as ⊗Eq
import Grammar.Epsilon.AsEquality Alphabet isSetAlphabet as εEq
import Grammar.Literal.AsEquality Alphabet isSetAlphabet as LiteralEq
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A B C D : Grammar ℓA

open MonoidalStr

MonoidalStr≡ : asPathMonoidalStr {ℓA} ≡ asEqualityMonoidalStr
MonoidalStr≡ i .ε = εEq.ε*≡ i
MonoidalStr≡ i .ε-intro = εEq.ε*-intro≡ i
MonoidalStr≡ i .ε-elim = εEq.ε*-elim≡ i
MonoidalStr≡ i .literal c = LiteralEq.literal*≡ c i
MonoidalStr≡ i .lit-intro = LiteralEq.lit*-intro≡ i
MonoidalStr≡ i ._⊗_ A B = ⊗Eq.⊗Path≡⊗Eq A B i
MonoidalStr≡ i .⊗-intro f g = ⊗Eq.⊗-intro≡ {f = f} {g = g} i
MonoidalStr≡ i .⊗-unit-r = {!⊗Eq.⊗-unit-r≡ i!}
MonoidalStr≡ i .⊗-unit-r⁻ = {!!}
MonoidalStr≡ i .⊗-unit-l = {!!}
MonoidalStr≡ i .⊗-unit-l⁻ = {!!}
MonoidalStr≡ i .⊗-assoc = {!!}
MonoidalStr≡ i .⊗-assoc⁻ = {!!}
