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
open import Term Alphabet
open import Helper

open import DFA.Base Alphabet
open import NFA.Base Alphabet
open import NFA.Regex.Base Alphabet
open import NFA.Determinization Alphabet

private
  variable
    ℓ : Level

-- open NFA

module ParseRegex
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where
  -- Regex to determinized DFA
  -- States are the ε-closed sets of states in the
  -- NFA that is equivalent to the regex
  regex→DFA : RegularExpression → DFA
  regex→DFA regex = (εClosedℙQ , isFinSet-εClosedℙQ) , ℙN
    where
    nfa : NFA ℓ-zero
    nfa = regex→NFA regex

    open Determinization nfa
      isFinSetAlphabet
      (isFinOrdStates regex)
      (isFinOrdTransition regex)
      (isFinOrdεTransition regex)

  module _ (regex : RegularExpression) where
    private
      dfa = regex→DFA regex
      states = dfa .fst

    module Aut = DeterministicAutomaton (dfa .snd)

    init = Aut.init
    Trace = Aut.Trace
    Parse = Aut.Trace true Aut.init

    run : string ⊢ ⊕[ b ∈ Bool ] Aut.Trace b Aut.init
    run = Aut.parseInit
