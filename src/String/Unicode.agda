{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.Unicode where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Erased.Data.Bool.Base
open import Erased.Data.Maybe.Base as Maybe
open import Erased.Data.List
open import Erased.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

import Erased.Data.Equality as Eq
open import Erased.Relation.Nullary.Base
open import Erased.Relation.Nullary.Properties

import Data.String.Properties as AgdaStdlibString
import Data.Char.Properties as AgdaStdlibChar
import Relation.Nullary.Decidable.Core as AgdaStdlibDec
import Relation.Nullary.Reflects as AgdaStdlibReflects
import Data.Empty as AgdaStdlibEmpty

UnicodeChar = Char
UnicodeString = String

charDecEq : DecEq UnicodeChar
charDecEq c c' with c AgdaStdlibChar.≟ c'
... | true AgdaStdlibDec.because AgdaStdlibReflects.ofʸ a = yes a
... | false AgdaStdlibDec.because AgdaStdlibReflects.ofⁿ ¬a = no (λ x → AgdaStdlibEmpty.⊥-elim (¬a x))

postulate
  mkUnicodeCharPath-yes : (c c' : UnicodeChar) → primCharEquality c c' ≡ true → c ≡ c'
  mkUnicodeCharPath-no : (c c' : UnicodeChar) → primCharEquality c c' ≡ false → ¬ (c ≡ c')

@0 DiscreteUnicodeChar : Discrete UnicodeChar
DiscreteUnicodeChar c c' =
  decRec
    (λ t → yes (mkUnicodeCharPath-yes c c' t))
    (λ f → no (mkUnicodeCharPath-no c c' (flip (primCharEquality c c') f)))
    (primCharEquality c c' ≟ true)
    where
    flip : (b : Bool) → ¬ (b ≡ true) → b ≡ false
    flip false _ = refl
    flip true ¬t=t = Empty.rec (¬t=t refl)

@0 isSetUnicodeChar : isSet UnicodeChar
isSetUnicodeChar = Discrete→isSet DiscreteUnicodeChar

module DecodeUnicode
  (Alphabet : Type ℓ-zero)
  (@0 isSetAlphabet : isSet Alphabet)
  (readUnicode : UnicodeChar → Maybe Alphabet)
  where

  mkString : String → List Alphabet
  mkString w = filterMap readUnicode (primStringToList w)

UnicodeChar→UnicodeString : UnicodeChar → UnicodeString
UnicodeChar→UnicodeString = primShowChar
