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

  acc? : Q .fst → Grammar ℓN
  acc? q = DecProp-grammar' {ℓG = ℓN} (isAcc q)

  rej? : Q .fst → Grammar ℓN
  rej? q = DecProp-grammar' {ℓG = ℓN} (negateDecProp (isAcc q))

  module _ (q-start : Q .fst) where
    data Trace : (q-end : Q .fst) → Grammar ℓN where
      nil : ε-grammar ⊢ Trace q-start
      cons : ∀ tr →
        Trace (src tr) ⊗ literal (label tr) ⊢ Trace (dst tr)
      ε-cons : ∀ εtr →
        Trace (ε-src εtr) ⊢ Trace (ε-dst εtr)

    record Algebra : Typeω where
      field
        the-ℓs : Q .fst → Level
        P : (q-end : Q .fst) → Grammar (the-ℓs q-end)
        nil-case : ε-grammar ⊢ P q-start
        cons-case : ∀ tr →
          P (src tr) ⊗ literal (label tr) ⊢ P (dst tr)
        ε-cons-case : ∀ εtr →
          P (ε-src εtr) ⊢ P (ε-dst εtr)

    open Algebra

    record AlgebraHom (alg alg' : Algebra) : Typeω where
      field
        f : (q-end : Q .fst) → alg .P q-end ⊢ alg' .P q-end
        on-nil :
          Path (ε-grammar ⊢ alg' .P q-start)
            (seq {h = alg .P q-start}
              (alg .nil-case)
              (f q-start))
            (alg' .nil-case)
        on-cons : (tr : transition .fst) →
          Path (alg .P (src tr) ⊗ literal (label tr) ⊢ alg' .P (dst tr))
            (seq {h = alg .P (dst tr)}
              (alg .cons-case tr)
              (f (dst tr)))
            (seq {h = alg' .P (src tr) ⊗ literal (label tr)}
              (⊗-intro
                {g = alg .P (src tr)}{h = alg' .P (src tr)}
                {k = literal (label tr)}{l = literal (label tr)}
                (f (src tr))
                (id {g = literal (label tr)}))
              (alg' .cons-case tr))
        on-ε-cons : (εtr : ε-transition .fst) →
          Path (alg .P (ε-src εtr) ⊢ alg' .P (ε-dst εtr))
            ((alg .ε-cons-case εtr) ⋆ (f (ε-dst εtr)))
            (f (ε-src εtr) ⋆ alg' .ε-cons-case εtr)

-- --       open AlgebraHom

-- --       idAlgebraHom : (alg : Algebra) →
-- --         AlgebraHom alg alg
-- --       f (idAlgebraHom alg) q-start =
-- --         id {g = alg .P q-start}
-- --       on-nil (idAlgebraHom alg) _ = refl
-- --       on-cons (idAlgebraHom alg) _ _ = refl
-- --       on-ε-cons (idAlgebraHom alg) _ _ = refl

-- --       AlgebraHom-seq : {alg alg' alg'' : Algebra} →
-- --         AlgebraHom alg alg' → AlgebraHom alg' alg'' →
-- --         AlgebraHom alg alg''
-- --       f (AlgebraHom-seq ϕ ψ) q-end x =
-- --         ψ .f q-end (ϕ .f q-end x)
-- --       on-nil (AlgebraHom-seq ϕ ψ) p =
-- --         cong (ψ .f q-start) (ϕ .on-nil p) ∙
-- --         (ψ .on-nil p)
-- --       on-cons (AlgebraHom-seq ϕ ψ) tr (s , p , lit) =
-- --         cong (ψ .f (dst tr)) (ϕ .on-cons tr (s , p , lit)) ∙
-- --         (ψ .on-cons tr (s , (ϕ .f (src tr) p) , lit))
-- --       on-ε-cons (AlgebraHom-seq ϕ ψ) εtr p =
-- --         cong (ψ .f (ε-dst εtr)) (ϕ .on-ε-cons εtr p) ∙
-- --         ψ .on-ε-cons εtr (ϕ .f (ε-src εtr) p)

-- --       initial : Algebra
-- --       the-ℓs initial _ = ℓN
-- --       P initial = Trace
-- --       nil-case initial = nil
-- --       cons-case initial = cons
-- --       ε-cons-case initial = ε-cons

-- --       module _
-- --         (the-alg : Algebra)
-- --         where
-- --         recTrace : ∀ {q-end} → Trace q-end ⊢ the-alg .P q-end
-- --         recTrace (nil x) = the-alg .nil-case x
-- --         recTrace (cons tr x) =
-- --           the-alg .cons-case tr ((x .fst) ,
-- --             ((recTrace (x .snd .fst)) , (x .snd .snd)))
-- --         recTrace (ε-cons εtr x) = the-alg .ε-cons-case εtr (recTrace x)
-- --         -- the-alg .ε-cons εtr (recTrace x)

-- --         ∃AlgebraHom : AlgebraHom initial the-alg
-- --         f ∃AlgebraHom q-end = recTrace {q-end}
-- --         on-nil ∃AlgebraHom p = refl
-- --         on-cons ∃AlgebraHom tr p = refl
-- --         on-ε-cons ∃AlgebraHom εtr p = refl

-- --         !AlgebraHom :
-- --           (e : AlgebraHom initial the-alg) →
-- --           (q-end : Q .fst) →
-- --           Term≡ {g = Trace q-end} (e .f q-end) recTrace
-- --         !AlgebraHom e q-start (nil x) = e .on-nil x
-- --         !AlgebraHom e .(dst tr) (cons tr x) =
-- --           e .on-cons tr x ∙
-- --             cong (λ a → the-alg .cons-case tr (x .fst , a , x .snd .snd))
-- --               (!AlgebraHom e (src tr) (x .snd .fst))
-- --         !AlgebraHom e .(ε-dst εtr) (ε-cons εtr p) =
-- --           e .on-ε-cons εtr p ∙
-- --           cong (λ a → the-alg .ε-cons-case εtr a)
-- --             (!AlgebraHom e (ε-src εtr) p)

-- --       initial→initial≡id :
-- --         (e : AlgebraHom initial initial) →
-- --         (q-end : Q .fst) →
-- --         Term≡ {g = Trace q-end}
-- --           (e .f q-end)
-- --           (idAlgebraHom initial .f q-end)
-- --       initial→initial≡id e q-end p =
-- --         !AlgebraHom initial e q-end p ∙
-- --         sym
-- --           (!AlgebraHom initial (idAlgebraHom initial) q-end p)

-- --     Trace-syntax : Q .fst → Q .fst → Grammar ℓN
-- --     Trace-syntax q-start q-end = Trace q-start q-end
-- --     syntax Trace-syntax q-start q-end = [ q-start →* q-end ]

-- --     module _ (q-start q-mid : Q .fst) where
-- --       open Algebra
-- --       the-concat-alg : Algebra q-mid
-- --       the-ℓs the-concat-alg _ = ℓN
-- --       P the-concat-alg q-end = [ q-start →* q-mid ] -⊗ [ q-start →* q-end ]
-- --       nil-case the-concat-alg =
-- --         -⊗-intro {g = [ q-start →* q-mid ]} {h = ε-grammar}
-- --           {k = [ q-start →* q-mid ]}
-- --           (ε-extension-r {g = ε-grammar} {h = [ q-start →* q-mid ]}
-- --             {k = [ q-start →* q-mid ]}
-- --             (id {g = ε-grammar})
-- --             (id {g = [ q-start →* q-mid ]}))
-- --       cons-case the-concat-alg tr =
-- --         -⊗-intro {g = [ q-start →* q-mid ]}
-- --           {h = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]) ⊗ literal (label tr)}
-- --           {k = [ q-start →* dst tr ]}
-- --           (⊗-assoc-inv {g = [ q-start →* q-mid ]}
-- --             {h = [ q-start →* q-mid ] -⊗ [ q-start →* src tr ]}
-- --             {k = literal (label tr)}
-- --             {l = [ q-start →* dst tr ]}
-- --             (trans
-- --               {g = ([ q-start →* q-mid ] ⊗
-- --                 ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]))
-- --                 ⊗ literal (label tr)}
-- --               {h = [ q-start →* src tr ] ⊗ literal (label tr)}
-- --               {k = [ q-start →* dst tr ]}
-- --               (cut
-- --                 {g = [ q-start →* q-mid ] ⊗
-- --                   ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
-- --                 {h = [ q-start →* src tr ]}
-- --                 (var ⊗l literal (label tr))
-- --                 (-⊗-elim {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
-- --                   {h = [ q-start →* q-mid ]} {k = [ q-start →* src tr ]}
-- --                   {l = [ q-start →* q-mid ]}
-- --                   (id {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])} )
-- --                   (id {g = [ q-start →* q-mid ]})))
-- --               (cons tr)))
-- --       ε-cons-case the-concat-alg εtr =
-- --         cut {g = [ q-start →* ε-src εtr ]}
-- --           {h = [ q-start →* ε-dst εtr ]}
-- --           ([ q-start →* q-mid ] -⊗OH var)
-- --           (ε-cons εtr)

-- --     open AlgebraHom
-- --     concatTrace : ∀ {q-start}{q-mid}{q-end} →
-- --       [ q-start →* q-mid ] ⊗ [ q-mid →* q-end ] ⊢ [ q-start →* q-end ]
-- --     concatTrace {q-start}{q-mid}{q-end} =
-- --       -⊗-elim
-- --        {g = [ q-mid →* q-end ]}
-- --        {h = [ q-start →* q-mid ]} {k = [ q-start →* q-end ]}
-- --        {l = [ q-start →* q-mid ]}
-- --        (∃AlgebraHom q-mid (the-concat-alg q-start q-mid) .f q-end)
-- --        (id {g = [ q-start →* q-mid ]})

-- --     module _ (q-start : Q .fst) where
-- --       TraceFrom : Grammar ℓN
-- --       TraceFrom = LinearΣ (λ (q-end : Q .fst) → [ q-start →* q-end ])

-- --       AcceptingFrom : Grammar ℓN
-- --       AcceptingFrom =
-- --         LinearΣ
-- --           (λ ((q-end , isAcc-q-end ): Σ[ q ∈ Q .fst ] isAcc q .fst .fst) →
-- --              [ q-start →* q-end ])

-- --     Parses : Grammar ℓN
-- --     Parses = AcceptingFrom init

-- -- open NFADefs
-- -- open NFA

-- -- module TraceSyntax (Σ₀ : Type ℓ-zero) where

-- --   Trace-syntax' : ∀ {ℓN} →
-- --     (N : NFA ℓN Σ₀) →
-- --     Q N .fst → Q N .fst → Grammar ℓN
-- --   Trace-syntax' N = Trace N
-- --   syntax Trace-syntax' N q-start q-end = ⟨ N ⟩[ q-start →* q-end ]
