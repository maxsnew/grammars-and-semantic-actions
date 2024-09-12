open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

record DFA : Type (ℓ-suc ℓD) where
  field
    Q : FinSet ℓD
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → DecProp ℓD
    δ : ⟨ Q ⟩ → ⟨ Alphabet ⟩ → ⟨ Q ⟩

  negate : DFA
  Q negate = Q
  init negate = init
  isAcc negate q = negateDecProp (isAcc q)
  δ negate = δ

  module _ (q-end : ⟨ Q ⟩) where
    -- The grammar "Trace q" denotes the type of traces in the DFA
    -- from state q to q-end
    data Trace : (q : ⟨ Q ⟩) → Grammar ℓD where
      nil : ε ⊢ Trace q-end
      cons : ∀ q c →
        literal c ⊗ Trace (δ q c) ⊢ Trace q

    record Algebra : Typeω where
      field
        the-ℓs : ⟨ Q ⟩ → Level
        G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
        nil-case : ε ⊢ G q-end
        cons-case : ∀ q c →
          literal c ⊗ G (δ q c) ⊢ G q

    open Algebra

    initial : Algebra
    the-ℓs initial _ = ℓD
    G initial = Trace
    nil-case initial = nil
    cons-case initial = cons

    record AlgebraHom (alg alg' : Algebra) : Typeω where
      field
        f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
        on-nil :
          f q-end ∘g alg .nil-case ≡ alg' .nil-case
        on-cons : ∀ q c →
          f q ∘g alg .cons-case q c ≡
            alg' .cons-case q c ∘g (⊗-intro id (f (δ q c)))
      fInit = f init

    open AlgebraHom

    idAlgebraHom : (alg : Algebra) →
      AlgebraHom alg alg
    f (idAlgebraHom alg) q = id
    on-nil (idAlgebraHom alg) = refl
    on-cons (idAlgebraHom alg) _ _ = refl

    AlgebraHom-seq : {alg alg' alg'' : Algebra} →
      AlgebraHom alg alg' → AlgebraHom alg' alg'' →
      AlgebraHom alg alg''
    AlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
    AlgebraHom-seq ϕ ψ .on-nil =
      cong (ψ .f _ ∘g_) (ϕ .on-nil)  ∙
      ψ .on-nil
    AlgebraHom-seq ϕ ψ .on-cons q c =
      cong (ψ .f q ∘g_) (ϕ .on-cons q c) ∙
      cong (_∘g ⊗-intro id (ϕ .f (δ q c))) (ψ .on-cons q c)

    module _ (the-alg : Algebra) where
      recTrace : ∀ {q} → Trace q ⊢ the-alg .G q
      recTrace {q} w (nil .w pε) = the-alg .nil-case w pε
      recTrace {q} w (cons .q c .w p⊗) =
        the-alg .cons-case q c _
          (p⊗ .fst , (p⊗ .snd .fst) , (recTrace _ (p⊗ .snd .snd)))

      recInit : Trace init ⊢ the-alg .G init
      recInit = recTrace

      ∃AlgebraHom : AlgebraHom initial the-alg
      f ∃AlgebraHom q = recTrace {q}
      on-nil ∃AlgebraHom = refl
      on-cons ∃AlgebraHom _ _ = refl

      !AlgebraHom-help :
        (e : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        (∀ w p → e .f q w p ≡ recTrace w p)
      !AlgebraHom-help e q w (nil .w pε) =
        cong (λ a → a w pε) (e .on-nil)
      !AlgebraHom-help e q w (cons .q c .w p⊗) =
        cong (λ a → a w p⊗) (e .on-cons q c) ∙
        cong (λ a → the-alg .cons-case q c _
          ((p⊗ .fst) , ((p⊗ .snd .fst) , a)))
          (!AlgebraHom-help e (δ q c) _
            (p⊗ .snd .snd))

      !AlgebraHom :
        (e : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ recTrace {q}
      !AlgebraHom e q =
        funExt (λ w → funExt (λ p → !AlgebraHom-help e q w p))

      -- TODO rename
      !AlgebraHom' :
        (e e' : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ e' .f q
      !AlgebraHom' e e' q =
        !AlgebraHom e q ∙
        sym (!AlgebraHom e' q)

    initial→initial≡id :
      (e : AlgebraHom initial initial) →
      (q : ⟨ Q ⟩) →
      (e .f q)
         ≡
      id
    initial→initial≡id e q =
      !AlgebraHom initial e q ∙
      sym (!AlgebraHom initial (idAlgebraHom initial) q)

    algebra-η :
      (e : AlgebraHom initial initial) →
      fInit e ≡ id
    algebra-η e = initial→initial≡id e _

  module _ (q-start : ⟨ Q ⟩) where
    module _ (q-end : ⟨ Q ⟩) where
      AcceptingTrace : Grammar ℓD
      AcceptingTrace =
        LinΣ[ acc ∈ ⟨ isAcc q-end .fst ⟩ ] Trace q-end q-start

      RejectingTrace : Grammar ℓD
      RejectingTrace =
        LinΣ[ acc ∈ (⟨ isAcc q-end .fst ⟩ → Empty.⊥) ] Trace q-end q-start

      open StrongEquivalence
      ¬AcceptingTrace≅RejectingTrace :
        StrongEquivalence
          (¬ AcceptingTrace)
          RejectingTrace
      ¬AcceptingTrace≅RejectingTrace .fun =
        {!!}
      ¬AcceptingTrace≅RejectingTrace .inv =
        ⇒-intro
          (⇒-intro⁻ (LinΣ-elim (λ rej →
            ⇒-intro (⇒-intro⁻ (LinΣ-elim (λ acc →
              Empty.rec (rej acc))) ∘g
            &-intro &-π₂ &-π₁))))
      ¬AcceptingTrace≅RejectingTrace .sec = {!!}
      ¬AcceptingTrace≅RejectingTrace .ret = {!!}

    TraceFrom : Grammar ℓD
    TraceFrom = LinΣ[ q-end ∈ ⟨ Q ⟩ ] Trace q-end q-start

    AcceptingTraceFrom : Grammar ℓD
    AcceptingTraceFrom =
      LinΣ[ q-end ∈ ⟨ Q ⟩ ] LinΣ[ q-end ∈ ⟨ Q ⟩ ] Trace q-end q-start

    ParseFrom : Grammar ℓD
    ParseFrom =
      LinΣ[ q-end ∈ (Σ[ q ∈ ⟨ Q ⟩ ] isAcc q .fst .fst) ]
        Trace (q-end .fst) q-start

  InitTrace : Grammar ℓD
  InitTrace = TraceFrom init

  InitParse : Grammar ℓD
  InitParse = ParseFrom init

