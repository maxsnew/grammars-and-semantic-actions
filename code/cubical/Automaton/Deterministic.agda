open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automaton.Deterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Equivalence Alphabet
import Cubical.Data.Equality as Eq
open import Term Alphabet
open import Helper

private
  variable ℓ ℓ' : Level

record DeterministicAutomaton ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Q : Type ℓ
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag : Type where
    stop step : Tag

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → ⊗e (k (literal* c)) (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)
