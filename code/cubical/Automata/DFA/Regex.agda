open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automata.DFA.Regex (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Term Alphabet

open import Automata.DFA.Base Alphabet
open import Automata.NFA.Base Alphabet
open import Thompson.Base Alphabet
open import Determinization.WeakEquivalence Alphabet

private
  variable
    ℓ : Level

module ParseRegex
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where
  module _ (regex : RegularExpression) where
    private
      nfa : NFA ℓ-zero
      nfa = regex→NFA regex

    open Determinization nfa
      isFinSetAlphabet
      (isFinOrdStates regex)
      (isFinOrdTransition regex)
      (isFinOrdεTransition regex)

    -- Regex to determinized DFA
    -- States are the ε-closed sets of states in the
    -- NFA that is equivalent to the regex
    regex→DFA : DFA
    regex→DFA = (εClosedℙQ , isFinSet-εClosedℙQ) , ℙN

    private
      dfa = regex→DFA
      states = dfa .fst

    module Aut = DeterministicAutomaton (dfa .snd)

    init = Aut.init
    Trace = Aut.Trace
    Parse = Aut.Trace true Aut.init

    run : string ⊢ ⊕[ b ∈ Bool ] Aut.Trace b Aut.init
    run = Aut.parseInit

    run' : (s : String) → (⊕[ b ∈ Bool ] Aut.Trace b Aut.init) s
    run' = parse-string run
