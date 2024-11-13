open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Regex (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.RegularExpression Alphabet
open import Grammar.Equivalence.Base Alphabet

open import DFA.Base Alphabet
open import NFA.Regex.StrongEquivalence Alphabet
open import NFA.Determinization Alphabet

private
  variable
    ℓ : Level

regex→DFA : RegularExpression → DFA {!!}
regex→DFA regex =
  let nfa = regex→NFA regex in
  {!!}

