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

  run-from-state : string-grammar ⊢ LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q
  run-from-state = foldKL*r char the-alg
    where
    the-alg : *r-Algebra char
    the-alg .the-ℓ = ℓD
    the-alg .G = LinΠ[ q ∈ ⟨ Q ⟩ ] TraceFrom q
    the-alg .nil-case = LinΠ-intro (λ q → LinΣ-intro q ∘g nil)
    the-alg .cons-case = LinΠ-intro (λ q →
      ⟜-intro⁻ (LinΣ-elim (λ c →
        ⟜-intro {k = TraceFrom q}
          (⊸-intro⁻
            (LinΣ-elim
              (λ q' → ⊸-intro {k = TraceFrom q}
                (LinΣ-intro {h = λ q'' → Trace q'' q} q' ∘g
                  Trace.cons q c))
            ∘g LinΠ-app (δ q c))))))

  check-accept : {q-start : ⟨ Q ⟩} (q-end : ⟨ Q ⟩) →
    Trace q-end q-start ⊢
      AcceptingTrace q-start q-end ⊕ RejectingTrace q-start q-end
      -- LinΣ[ acc? ∈ ⟨ isAcc q-end .fst ⟩ ⊎ (⟨ isAcc q-end .fst ⟩ → Empty.⊥) ]
      --   Trace q-end q-start
  check-accept q =
    decRec
      (λ acc → ⊕-inl ∘g LinΣ-intro acc)
      (λ rej → ⊕-inr ∘g LinΣ-intro rej)
      (isAcc q .snd)

  -- TODO unsure which equivalence we want for the decider
  open StrongEquivalence
  module _ (q-start : ⟨ Q ⟩) where
    ¬AcceptingTraceFrom≅RejectingTraceFrom :
      StrongEquivalence
        (¬ AcceptingTraceFrom q-start)
        (RejectingTraceFrom q-start)
    ¬AcceptingTraceFrom≅RejectingTraceFrom .fun = {!!}
    ¬AcceptingTraceFrom≅RejectingTraceFrom .inv = {!!}
    ¬AcceptingTraceFrom≅RejectingTraceFrom .sec = {!!}
    ¬AcceptingTraceFrom≅RejectingTraceFrom .ret = {!!}
  module _ (q-start q-end : ⟨ Q ⟩) where
    ¬AcceptingTrace≅RejectingTrace :
      StrongEquivalence
        (¬ AcceptingTrace q-start q-end)
        (RejectingTrace q-start q-end)
    ¬AcceptingTrace≅RejectingTrace .fun =
      {!!}
      -- {!!} ∘g
      -- {!!} ∘g
      -- -- &-par (LinΣ-elim (λ q-end' → {!check-accept {q-start} q-end'!}) ∘g LinΠ-app q-start) id ∘g
      -- &-intro (run-from-state ∘g ⊤→string ∘g ⊤-intro) id
    ¬AcceptingTrace≅RejectingTrace .inv =
      ⇒-intro
        (⇒-intro⁻ (LinΣ-elim (λ rej →
          ⇒-intro (⇒-intro⁻ (LinΣ-elim (λ acc →
            Empty.rec (rej acc))) ∘g
          &-intro &-π₂ &-π₁))))
    ¬AcceptingTrace≅RejectingTrace .sec = {!!}
    ¬AcceptingTrace≅RejectingTrace .ret = {!!}
  -- run : string-grammar ⊢ InitTrace
  -- run = LinΠ-app init ∘g run-from-state

  -- decide :
  --   string-grammar ⊢ LinΣ[ b ∈ Bool ] InitTrace
  -- decide =
  --   LinΣ-elim (λ q → check-accept q) ∘g
  --   run


  decidableDFA : decidable (LinΠ[ q ∈ ⟨ Q ⟩ ] AcceptingTraceFrom q)
  decidableDFA .fun =
    {!!}
  decidableDFA .inv =
    {!!} ∘g
    {!!}
  decidableDFA .sec = {!!}
  decidableDFA .ret = {!!}
