open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Decider (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
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

  check-accept : {q-start : ⟨ Q ⟩} (q : ⟨ Q ⟩) →
    Trace q q-start ⊢ LinΣ[ b ∈ Bool ] TraceFrom q-start
  check-accept q =
    LinΣ-intro
      (decRec (λ _ → true) (λ _ → false) (isAcc q .snd)) ∘g
    LinΣ-intro q

  run : string-grammar ⊢ InitTrace
  run = LinΠ-app init ∘g run-from-state

  decide :
    string-grammar ⊢ LinΣ[ b ∈ Bool ] InitTrace
  decide =
    LinΣ-elim (λ q → check-accept q) ∘g
    run
