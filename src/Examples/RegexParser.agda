open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module Examples.RegexParser (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Term Alphabet
open import Parser Alphabet
open import Determinization.WeakEquivalence Alphabet
open import Thompson.Base Alphabet
open import Thompson.Equivalence Alphabet
open import Automata.NFA.Base Alphabet as NFA
import Automata.NFA.Properties Alphabet as NFAEq
open import Automata.Deterministic Alphabet

open NFA.Accepting hiding (Trace)

module _ (r : RegularExpression)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩ )
  where
  open Determinization (regex→NFA r) isFinSetAlphabet
    (isFinOrdStates r) (isFinOrdTransition r) (isFinOrdεTransition r)
  open DeterministicAutomaton ℙN

  regex≈DFA : ⟦ r ⟧r ≈ Trace true init
  regex≈DFA =
    ≅→≈ (sym≅ (regex≅NFA r) ≅∙ NFAEq.Trace≅ (regex→NFA r) (NFA.init (regex→NFA r)))
    ≈∙ NFA≈DFA

  regexParser : Parser ⟦ r ⟧r (Trace false init)
  regexParser = ≈Parser (AccTraceParser init) (sym≈ regex≈DFA)
