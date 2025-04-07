open import Erased.Foundations.Prelude

open import Erased.Relation.Nullary

module String.Alphabet where

record AlphabetOver (A : Type) : Type where
  field
   is-discrete : DiscreteEq A

Alphabet : Type (ℓ-suc ℓ-zero)
Alphabet = Σ Type AlphabetOver
