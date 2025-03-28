open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.Unicode where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.List
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import String.SubAlphabet


UnicodeChar = Char
UnicodeString = String

-- Char equality is computed externally by JavaScript
-- Internalize a path oracle
postulate
  mkUnicodeCharPath-yes : (c c' : UnicodeChar) → primCharEquality c c' ≡ true → c ≡ c'
  mkUnicodeCharPath-no : (c c' : UnicodeChar) → primCharEquality c c' ≡ false → ¬ (c ≡ c')

DiscreteUnicodeChar : Discrete UnicodeChar
DiscreteUnicodeChar c c' =
  decRec
    (λ t → yes (mkUnicodeCharPath-yes c c' t))
    (λ f → no (mkUnicodeCharPath-no c c' (flip (primCharEquality c c') f)))
    (primCharEquality c c' ≟ true)
    where
    flip : (b : Bool) → ¬ (b ≡ true) → b ≡ false
    flip false _ = refl
    flip true ¬t=t = Empty.rec (¬t=t refl)

isSetUnicodeChar : isSet UnicodeChar
isSetUnicodeChar = Discrete→isSet DiscreteUnicodeChar

-- The unicode alphabet
Unicode : hSet ℓ-zero
Unicode .fst = UnicodeChar
Unicode .snd = isSetUnicodeChar

module DecodeUnicode
  (Alphabet : hSet ℓ-zero)
  (readUnicode : UnicodeChar → Maybe ⟨ Alphabet ⟩)
  where

  mkString : String → List ⟨ Alphabet ⟩
  mkString w = filterMap readUnicode (primStringToList w)
