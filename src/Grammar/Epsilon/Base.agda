open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Epsilon.Interface Alphabet public
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

import Grammar.Epsilon.AsEquality.Base Alphabet as asEquality
import Grammar.Epsilon.AsPath.Base Alphabet as asPath

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

open εStr

module εAsEquality where
  instance
    εAsEquality : εStr
    εAsEquality .ε = asEquality.ε
    εAsEquality .ε-intro = asEquality.ε-intro
    εAsEquality .ε-elim = asEquality.ε-elim
    εAsEquality .ε-elim-natural = asEquality.ε-elim-natural
    εAsEquality .ε-β = asEquality.ε-β
    εAsEquality .isLangε = asEquality.isLangε
    εAsEquality .ε-length0 = asEquality.ε-length0

module ε*AsEquality where
  instance
    ε*AsEquality : εStr
    ε*AsEquality .ε = asEquality.ε*
    ε*AsEquality .ε-intro = lift (εAsEquality.εAsEquality .ε-intro)
    ε*AsEquality .ε-elim A[] = εAsEquality.εAsEquality .ε-elim A[] ∘g lowerG
    ε*AsEquality .ε-elim-natural A[] f = cong (_∘g lowerG) (εAsEquality.εAsEquality .ε-elim-natural A[] f)
    ε*AsEquality .ε-β = εAsEquality.εAsEquality .ε-β
    ε*AsEquality .isLangε = asEquality.isLangε*
    ε*AsEquality .ε-length0 w p = εAsEquality.εAsEquality .ε-length0 w (lower p)

module εAsPath where
  instance
    @0 εAsPath : εStr
    εAsPath .ε = asPath.ε
    εAsPath .ε-intro = asPath.ε-intro
    εAsPath .ε-elim = asPath.ε-elim
    εAsPath .ε-elim-natural = asPath.ε-elim-natural
    εAsPath .ε-β = asPath.ε-β
    εAsPath .isLangε = asPath.isLangε
    εAsPath .ε-length0 = asPath.ε-length0

module ε*AsPath where
  instance
    @0 ε*AsPath : εStr
    ε*AsPath .ε = asPath.ε*
    ε*AsPath .ε-intro = lift (εAsPath.εAsPath .ε-intro)
    ε*AsPath .ε-elim A[] = εAsPath.εAsPath .ε-elim A[] ∘g lowerG
    ε*AsPath .ε-elim-natural A[] f = cong (_∘g lowerG) (εAsPath.εAsPath .ε-elim-natural A[] f)
    ε*AsPath .ε-β = εAsPath.εAsPath .ε-β
    ε*AsPath .isLangε = asPath.isLangε*
    ε*AsPath .ε-length0 w p = εAsPath.εAsPath .ε-length0 w (lower p)
