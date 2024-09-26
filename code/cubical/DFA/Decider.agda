open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Decider (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module _ (D : DFA {ℓD}) where
  open DFA D

  open *r-Algebra
  open Algebra
  open AlgebraHom

  opaque
    unfolding _⊗_
    run-from-state : string ⊢ LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q
    run-from-state = foldKL*r char the-alg
      where
        the-cons :
          char ⊗ LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q ⊢
            LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q
        the-cons =
          LinΠ-intro (λ q →
          ⟜-intro⁻ (LinΣ-elim (λ c →
            ⟜-intro {k = TraceFrom q}
              (⊸-intro⁻
                (LinΣ-elim
                  (λ q' → ⊸-intro {k = TraceFrom q}
                    (LinΣ-intro {h = λ q'' → Trace q'' q} q' ∘g
                      Trace.cons q c))
                ∘g LinΠ-app (δ q c))))))

        the-alg : *r-Algebra char
        the-alg .the-ℓ = ℓD
        the-alg .G = LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q
        the-alg .nil-case = LinΠ-intro (λ q → LinΣ-intro q ∘g nil)
        the-alg .cons-case = the-cons

  check-accept : {q-start : ⟨ Q ⟩} (q-end : ⟨ Q ⟩) →
    Trace q-end q-start ⊢
      AcceptingTrace q-start q-end ⊕ RejectingTrace q-start q-end
  check-accept q =
    decRec
      (λ acc → ⊕-inl ∘g LinΣ-intro acc)
      (λ rej → ⊕-inr ∘g LinΣ-intro rej)
      (isAcc q .snd)

  check-accept-from : (q-start : ⟨ Q ⟩) →
    TraceFrom q-start ⊢
      AcceptingTraceFrom q-start ⊕ RejectingTraceFrom q-start
  check-accept-from q-start =
    LinΣ-elim (λ q-end →
      ⊕-elim (⊕-inl ∘g LinΣ-intro q-end) (⊕-inr ∘g LinΣ-intro q-end) ∘g
      check-accept q-end)

  decide :
    string ⊢
      LinΠ[ q ∈ ⟨ Q ⟩ ] (AcceptingTraceFrom q ⊕ RejectingTraceFrom q)
  decide =
    LinΠ-intro (λ q →
      check-accept-from q ∘g
      LinΠ-app q) ∘g
    run-from-state

  decideInit :
    string ⊢
      (AcceptingTraceFrom init ⊕ RejectingTraceFrom init)
  decideInit = LinΠ-app init ∘g decide
