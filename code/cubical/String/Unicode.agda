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

-- I thought this would be good to define alphabets, but
-- that cannot be true because you cannot pattern match on the characters
-- in an alphabet due to the paths in the fibers underlying the subalphabet
-- definitions
-- However, this should still be good to write test cases more concisely?
-- Still likely no. Maybe if Eq was used instead of path?
module _
  (Alphabet : hSet ℓ-zero)
  (embed : ⟨ Alphabet ⟩ ↪ ⟨ Unicode ⟩)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where
  UnicodeSubAlphabet : hSet ℓ-zero
  UnicodeSubAlphabet = SubAlphabet Alphabet Unicode embed

  -- This should probably be a stricter check that none of the
  -- characters were from outside of the subalphabet
  toString : String → List ⟨ UnicodeSubAlphabet ⟩
  toString w =
    filterMap
      (maybe-SubAlphabet Alphabet Unicode embed
        isFinSetAlphabet DiscreteUnicodeChar)
      (primStringToList w)
