open import Erased.Foundations.Prelude

open import Erased.Relation.Nullary

module String.Alphabet where

record AlphabetOver (A : Type) : Type where
  field
   is-discrete : Discrete A

  @0 is-set : isSet A
  is-set = Discrete→isSet is-discrete

Alphabet : Type (ℓ-suc ℓ-zero)
Alphabet = Σ Type AlphabetOver
