{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.Conversion (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.Epsilon.AsEquality Alphabet
open import Grammar.Epsilon.AsPath Alphabet
  renaming (ε to εPath)
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  unfolding ε εPath
  ε→εPath : ε ⊢ εPath
  ε→εPath w = Eq.eqToPath

  εPath→ε : εPath ⊢ ε
  εPath→ε w = Eq.pathToEq

  ε→εPath→ε : εPath→ε ∘g ε→εPath ≡ id
  ε→εPath→ε = funExt λ w → funExt Eq.pathToEq-eqToPath

  εPath→ε→εPath : ε→εPath ∘g εPath→ε ≡ id
  εPath→ε→εPath = funExt λ w → funExt Eq.eqToPath-pathToEq

open StrongEquivalence

ε≅εPath : ε ≅ εPath
ε≅εPath .fun = ε→εPath
ε≅εPath .inv = εPath→ε
ε≅εPath .sec = εPath→ε→εPath
ε≅εPath .ret = ε→εPath→ε
