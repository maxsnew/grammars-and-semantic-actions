open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Equivalence Alphabet
import Cubical.Data.Equality as Eq
open import Term Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

record DFA : Type (ℓ-suc ℓ-zero) where
  field
    Q : FinSet ℓ-zero
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → Bool
    δ : ⟨ Q ⟩ → ⟨ Alphabet ⟩ → ⟨ Q ⟩

  data TraceTag : Type where
    stop step : TraceTag

  TraceTy : Bool → (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
  TraceTy b q = ⊕e TraceTag λ {
    stop → ⊕e (b Eq.≡ isAcc q) λ { Eq.refl → k ε }
    ; step → ⊕e ⟨ Alphabet ⟩ λ c → ⊗e (k (literal c)) (Var (δ q c)) }

  Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓ-zero
  Trace b = μ (TraceTy b)
