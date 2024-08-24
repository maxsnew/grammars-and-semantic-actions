-- {-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.NFA.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
open import Semantics.DFA
open import Semantics.Helper

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

record NFA : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN
    init : Q .fst
    isAcc : Q .fst → DecProp ℓN
    transition : FinSet ℓN
    src : transition .fst → Q .fst
    dst : transition .fst → Q .fst
    label : transition .fst → Σ₀
    ε-transition : FinSet ℓN
    ε-src : ε-transition .fst → Q .fst
    ε-dst : ε-transition .fst → Q .fst

  decEqQ : Discrete (Q .fst)
  decEqQ = isFinSet→Discrete (Q .snd)

  -- The grammar "Parse q" denotes the type of traces in the NFA
  -- from state q to an accepting state
  data Parse : (q : Q .fst) → Grammar ℓN where
    nil : ∀ {q} → isAcc q .fst .fst →
      ε-grammar ⊢ Parse q
    cons : ∀ tr →
      literal (label tr) ⊗ Parse (dst tr) ⊢ Parse (src tr)
    ε-cons : ∀ εtr →
      Parse (ε-dst εtr) ⊢ Parse (ε-src εtr)

  record Algebra : Typeω where
    field
      the-ℓs : Q .fst → Level
      G : (q : Q .fst) → Grammar (the-ℓs q)
      nil-case : ∀ {q} → isAcc q .fst .fst →
        ε-grammar ⊢ G q
      cons-case : ∀ tr →
        literal (label tr) ⊗ G (dst tr) ⊢ G (src tr)
      ε-cons-case : ∀ εtr →
        G (ε-dst εtr) ⊢ G (ε-src εtr)

  open Algebra

  record AlgebraHom (alg alg' : Algebra) : Typeω where
    field
      f : (q : Q .fst) → alg .G q ⊢ alg' .G q
      on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
        alg .nil-case qAcc ⋆ f q ≡ alg' .nil-case qAcc
      on-cons : (tr : transition .fst) →
        alg .cons-case tr ⋆ f (src tr) ≡
          (⊗-intro id (f (dst tr))) ⋆ alg' .cons-case tr
      on-ε-cons : (εtr : ε-transition .fst) →
        (alg .ε-cons-case εtr) ⋆ (f (ε-src εtr)) ≡
          f (ε-dst εtr) ⋆ alg' .ε-cons-case εtr

--     open AlgebraHom

--     idAlgebraHom : (alg : Algebra) →
--       AlgebraHom alg alg
--     f (idAlgebraHom alg) q-start = id
--     on-nil (idAlgebraHom alg) = refl
--     on-cons (idAlgebraHom alg) _ = refl
--     on-ε-cons (idAlgebraHom alg) _ = refl

--     AlgebraHom-seq : {alg alg' alg'' : Algebra} →
--       AlgebraHom alg alg' → AlgebraHom alg' alg'' →
--       AlgebraHom alg alg''
--     f (AlgebraHom-seq ϕ ψ) q-end _ x =
--       ψ .f q-end _ (ϕ .f q-end _ x)
--     on-nil (AlgebraHom-seq ϕ ψ) =
--       cong (λ t → t ⋆ ψ .f q-start) (ϕ .on-nil) ∙
--       ψ .on-nil
--     on-cons (AlgebraHom-seq ϕ ψ) tr =
--       cong (λ t → t ⋆ ψ .f (dst tr)) (ϕ .on-cons tr) ∙
--       cong (λ t → ⊗-intro (ϕ .f (src tr)) id ⋆ t) (ψ .on-cons tr)
--     on-ε-cons (AlgebraHom-seq ϕ ψ) εtr =
--       cong (λ t → t ⋆ ψ .f (ε-dst εtr)) (ϕ .on-ε-cons εtr) ∙
--       cong (λ t → ϕ .f (ε-src εtr) ⋆ t) (ψ .on-ε-cons εtr)

--     initial : Algebra
--     the-ℓs initial _ = ℓN
--     P initial = Trace
--     nil-case initial = nil
--     cons-case initial = cons
--     ε-cons-case initial = ε-cons

--     module _
--       (the-alg : Algebra)
--       where
--       recTrace : ∀ {q-end} → Trace q-end ⊢ the-alg .P q-end
--       recTrace _ (nil _ x) = the-alg .nil-case _ x
--       recTrace _ (cons tr _ x) =
--         the-alg .cons-case tr _ (x .fst , ((recTrace _ (x .snd .fst)) , x .snd .snd))
--       recTrace _ (ε-cons εtr _ x) =
--         the-alg .ε-cons-case εtr _ (recTrace _ x)

--       ∃AlgebraHom : AlgebraHom initial the-alg
--       f ∃AlgebraHom q-end = recTrace {q-end}
--       on-nil ∃AlgebraHom = refl
--       on-cons ∃AlgebraHom tr = refl
--       on-ε-cons ∃AlgebraHom εtr = refl

--       !AlgebraHom-help :
--         (e : AlgebraHom initial the-alg) →
--         (q-end : Q .fst) →
--         (∀ w p → e .f q-end w p ≡ recTrace w p)
--       !AlgebraHom-help e q-end w (nil .w x) =
--         cong (λ a → a w x) (e .on-nil)
--       !AlgebraHom-help e .(dst tr) w (cons tr .w x) =
--         cong (λ a → a w x) (e .on-cons tr) ∙
--         cong (λ a → the-alg .cons-case tr _ (x .fst , a , x .snd .snd))
--           (!AlgebraHom-help e (src tr) (x .fst .fst .fst) (x .snd .fst))
--       !AlgebraHom-help e .(ε-dst εtr) w (ε-cons εtr .w p) =
--         cong (λ a → a w p) (e .on-ε-cons εtr) ∙
--         cong (the-alg .ε-cons-case εtr w) (!AlgebraHom-help e (ε-src εtr) w p)

--       !AlgebraHom :
--         (e : AlgebraHom initial the-alg) →
--         (q-end : Q .fst) →
--         e .f q-end ≡ recTrace
--       !AlgebraHom e q-end = funExt (λ w → funExt (λ p → !AlgebraHom-help e q-end w p))

--     initial→initial≡id :
--       (e : AlgebraHom initial initial) →
--       (q-end : Q .fst) →
--       (e .f q-end)
--          ≡
--       (idAlgebraHom initial .f q-end)
--     initial→initial≡id e q-end =
--       !AlgebraHom initial e q-end ∙
--       sym (!AlgebraHom initial (idAlgebraHom initial) q-end)

-- -- --     Trace-syntax : Q .fst → Q .fst → Grammar ℓN
-- -- --     Trace-syntax q-start q-end = Trace q-start q-end
-- -- --     syntax Trace-syntax q-start q-end = [ q-start →* q-end ]

-- -- --     module _ (q-start q-mid : Q .fst) where
-- -- --       open Algebra
-- -- --       the-concat-alg : Algebra q-mid
-- -- --       the-ℓs the-concat-alg _ = ℓN
-- -- --       P the-concat-alg q-end = [ q-start →* q-mid ] -⊗ [ q-start →* q-end ]
-- -- --       nil-case the-concat-alg =
-- -- --         -⊗-intro {g = [ q-start →* q-mid ]} {h = ε-grammar}
-- -- --           {k = [ q-start →* q-mid ]}
-- -- --           (ε-extension-r {g = ε-grammar} {h = [ q-start →* q-mid ]}
-- -- --             {k = [ q-start →* q-mid ]}
-- -- --             (id {g = ε-grammar})
-- -- --             (id {g = [ q-start →* q-mid ]}))
-- -- --       cons-case the-concat-alg tr =
-- -- --         -⊗-intro {g = [ q-start →* q-mid ]}
-- -- --           {h = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]) ⊗ literal (label tr)}
-- -- --           {k = [ q-start →* dst tr ]}
-- -- --           (⊗-assoc-inv {g = [ q-start →* q-mid ]}
-- -- --             {h = [ q-start →* q-mid ] -⊗ [ q-start →* src tr ]}
-- -- --             {k = literal (label tr)}
-- -- --             {l = [ q-start →* dst tr ]}
-- -- --             (trans
-- -- --               {g = ([ q-start →* q-mid ] ⊗
-- -- --                 ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]))
-- -- --                 ⊗ literal (label tr)}
-- -- --               {h = [ q-start →* src tr ] ⊗ literal (label tr)}
-- -- --               {k = [ q-start →* dst tr ]}
-- -- --               (cut
-- -- --                 {g = [ q-start →* q-mid ] ⊗
-- -- --                   ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
-- -- --                 {h = [ q-start →* src tr ]}
-- -- --                 (var ⊗l literal (label tr))
-- -- --                 (-⊗-elim {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
-- -- --                   {h = [ q-start →* q-mid ]} {k = [ q-start →* src tr ]}
-- -- --                   {l = [ q-start →* q-mid ]}
-- -- --                   (id {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])} )
-- -- --                   (id {g = [ q-start →* q-mid ]})))
-- -- --               (cons tr)))
-- -- --       ε-cons-case the-concat-alg εtr =
-- -- --         cut {g = [ q-start →* ε-src εtr ]}
-- -- --           {h = [ q-start →* ε-dst εtr ]}
-- -- --           ([ q-start →* q-mid ] -⊗OH var)
-- -- --           (ε-cons εtr)

-- -- --     open AlgebraHom
-- -- --     concatTrace : ∀ {q-start}{q-mid}{q-end} →
-- -- --       [ q-start →* q-mid ] ⊗ [ q-mid →* q-end ] ⊢ [ q-start →* q-end ]
-- -- --     concatTrace {q-start}{q-mid}{q-end} =
-- -- --       -⊗-elim
-- -- --        {g = [ q-mid →* q-end ]}
-- -- --        {h = [ q-start →* q-mid ]} {k = [ q-start →* q-end ]}
-- -- --        {l = [ q-start →* q-mid ]}
-- -- --        (∃AlgebraHom q-mid (the-concat-alg q-start q-mid) .f q-end)
-- -- --        (id {g = [ q-start →* q-mid ]})

-- -- --     module _ (q-start : Q .fst) where
-- -- --       TraceFrom : Grammar ℓN
-- -- --       TraceFrom = LinearΣ (λ (q-end : Q .fst) → [ q-start →* q-end ])

-- -- --       AcceptingFrom : Grammar ℓN
-- -- --       AcceptingFrom =
-- -- --         LinearΣ
-- -- --           (λ ((q-end , isAcc-q-end ): Σ[ q ∈ Q .fst ] isAcc q .fst .fst) →
-- -- --              [ q-start →* q-end ])

-- -- --     Parses : Grammar ℓN
-- -- --     Parses = AcceptingFrom init

-- -- -- open NFADefs
-- -- -- open NFA

-- -- -- module TraceSyntax (Σ₀ : Type ℓ-zero) where

-- -- --   Trace-syntax' : ∀ {ℓN} →
-- -- --     (N : NFA ℓN Σ₀) →
-- -- --     Q N .fst → Q N .fst → Grammar ℓN
-- -- --   Trace-syntax' N = Trace N
-- -- --   syntax Trace-syntax' N q-start q-end = ⟨ N ⟩[ q-start →* q-end ]
