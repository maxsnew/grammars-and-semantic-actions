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
    string-grammar ⊢
      LinΠ[ q ∈ ⟨ Q ⟩ ] (AcceptingTraceFrom q ⊕ RejectingTraceFrom q)
  decide =
    LinΠ-intro (λ q →
      check-accept-from q ∘g
      LinΠ-app q) ∘g
    run-from-state
  -- open StrongEquivalence
  -- module _ (q-start q-end : ⟨ Q ⟩) where
  --   ¬AcceptingTrace≅RejectingTrace :
  --     StrongEquivalence
  --       (¬ AcceptingTrace q-start q-end)
  --       (RejectingTrace q-start q-end)
  --   ¬AcceptingTrace≅RejectingTrace .fun =
  --     {!!}
  --     -- {!!} ∘g
  --     -- {!!} ∘g
  --     -- -- &-par (LinΣ-elim (λ q-end' → {!check-accept {q-start} q-end'!}) ∘g LinΠ-app q-start) id ∘g
  --     -- &-intro (run-from-state ∘g ⊤→string ∘g ⊤-intro) id
  --   ¬AcceptingTrace≅RejectingTrace .inv =
  --     ⇒-intro
  --       (⇒-intro⁻ (LinΣ-elim (λ rej →
  --         ⇒-intro (⇒-intro⁻ (LinΣ-elim (λ acc →
  --           Empty.rec (rej acc))) ∘g
  --         &-intro &-π₂ &-π₁))))
  --   ¬AcceptingTrace≅RejectingTrace .sec = {!!}
  --   ¬AcceptingTrace≅RejectingTrace .ret = {!!}
  -- -- run : string-grammar ⊢ InitTrace
  -- -- run = LinΠ-app init ∘g run-from-state


  -- Trace→String : ∀ q-start q-end → Trace q-end q-start ⊢ string-grammar
  -- Trace→String q-start q-end =
  --   recTrace q-end the-alg
  --   where
  --   the-alg : Algebra q-end
  --   the-alg .the-ℓs = _
  --   the-alg .G _ = string-grammar
  --   the-alg .nil-case = KL*.nil
  --   the-alg .cons-case q c = KL*.cons ∘g LinΣ-intro c ,⊗ id

  -- TraceFrom≅string :
  --   ∀ q →
  --   StrongEquivalence
  --     (TraceFrom q)
  --     string-grammar
  -- TraceFrom≅string q .fun = LinΣ-elim (λ q' → Trace→String q q')
  -- TraceFrom≅string q .inv = LinΠ-app q ∘g run-from-state
  -- TraceFrom≅string q .sec = unabmiguous-string _ _ refl
  -- TraceFrom≅string q .ret =
  --   asdf (TraceFrom q) _ id (λ w p → {!!}) {!!}
  --   where
  --   asdf : ∀ {ℓg} (g : Grammar ℓg) →
  --     (e e' : g ⊢ LinΣ[ q' ∈ ⟨ Q ⟩ ] Trace q' q) →
  --     (∀ w p → e w p .fst ≡ e' w p .fst) →
  --     {!!} →
  --     e ≡ e'
  --   asdf = {!!}
  --   -- cong LinΣ-elim (funExt (λ q' →
  --   --   {!!}))
  --   -- Should be an algebra-η, but wrapped with a LinΣ

  -- totallyParseableDFA :
  --   ∀ q →
  --   totallyParseable (ParseFrom q)
  -- totallyParseableDFA q .fst = RejectingTraceFrom q
  -- totallyParseableDFA q .snd .fun = ⊤-intro
  -- totallyParseableDFA q .snd .inv =
  --   LinΠ-app q ∘g decide ∘g ⊤→string
  -- totallyParseableDFA q .snd .sec = unambiguous⊤ _ _ refl
  -- totallyParseableDFA q .snd .ret = {!!}

  -- decidableDFA : decidable (LinΠ[ q ∈ ⟨ Q ⟩ ] ParseFrom q)
  -- decidableDFA .fun = ⊤-intro
  -- decidableDFA .inv =
  --   {!!} ∘g
  --   {!!}
  -- decidableDFA .sec = unambiguous⊤ _ _ refl
  -- decidableDFA .ret = {!!}
