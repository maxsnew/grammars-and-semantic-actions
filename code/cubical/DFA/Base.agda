open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Base (Alphabet : hSet ℓ-zero) where

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
  variable ℓD ℓP ℓ : Level

record DFA : Type (ℓ-suc ℓD) where
  field
    Q : FinSet ℓD
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → Bool
    δ : ⟨ Q ⟩ → ⟨ Alphabet ⟩ → ⟨ Q ⟩

  data TraceTag : Type ℓD where
    stop step : TraceTag

  TraceTy : Bool → (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
  TraceTy b q = ⊕e TraceTag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q))
        λ { (lift Eq.refl) → k (LiftG ℓD ε) }
    ; step → ⊕e (Lift ⟨ Alphabet ⟩)
      λ { (lift c) → ⊗e (k (LiftG ℓD (literal c))) (Var (δ q c)) }}

  Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓD
  Trace b = μ (TraceTy b)
