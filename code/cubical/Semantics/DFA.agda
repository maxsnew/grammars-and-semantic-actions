{-# OPTIONS --lossy-unification #-}
module Semantics.DFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List hiding (init)
open import Cubical.Data.Unit
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma

open import Semantics.Grammar
open import Semantics.String
open import Semantics.Helper
open import Semantics.Term

private
  variable ℓ ℓ' : Level

module DFADefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open TermDefs ℓ (Σ₀ , isFinSetΣ₀)

  record DFA : Type (ℓ-suc ℓ) where
    constructor mkDFA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      δ : Q .fst → Σ₀ → Q .fst

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    Accepting : Type ℓ
    Accepting = Σ[ q ∈ Q .fst ] isAcc q .fst .fst

    acc? : Q .fst → Grammar
    acc? q = DecProp-grammar' (isAcc q)

    rej? : Q .fst → Grammar
    rej? q = DecProp-grammar' (negateDecProp (isAcc q))

    data DFATrace (q-end : Q .fst) : Q .fst → String → Type ℓ where
      nil : ε-grammar ⊢ (DFATrace q-end q-end)
      cons : ∀ q-start c →
          literal c ⊗ DFATrace q-end (δ q-start c) ⊢ DFATrace q-end q-start

    syntax DFATrace q-end q-start = DFA[ q-start →* q-end ]

    TraceFrom : (Q .fst) → Grammar
    TraceFrom q = LinΣ[ q' ∈ Q .fst ] DFA[ q →* q' ]

    module _ (q-end : Q .fst) where
      elimDFA :
        (P : ∀ q-start → Grammar) →
        (nil-case : ε-grammar ⊢ P q-end) →
        (cons-case : ∀ {q-start}{c} →
          literal c ⊗ P (δ q-start c) ⊢ (P q-start)) →
        ∀ {q-start} →
          DFA[ q-start →* q-end ] ⊢ P q-start
      elimDFA P nil-case cons-case (nil x) = nil-case x
      elimDFA P nil-case cons-case (cons q-start c x) =
        cons-case (x .fst , x .snd .fst , (elimDFA P nil-case cons-case (x .snd .snd)))

    data SnocDFATrace (q-start : Q .fst) : (q-end : Q .fst) → String → Type ℓ where
      nil : ε-grammar ⊢ (SnocDFATrace q-start q-start)
      snoc : ∀ q-end c →
        SnocDFATrace q-start q-end ⊗ literal c ⊢ SnocDFATrace q-start (δ q-end c)

    syntax SnocDFATrace q-start q-end = SnocDFA[ q-start →* q-end ]

    module _ (q-start : Q .fst) where
      elimSnocDFA :
        (P : ∀ q-end → Grammar) →
        (nil-case : ε-grammar ⊢ P q-start) →
        (snoc-case : ∀ {q-end}{c} →
          P q-end ⊗ literal c ⊢ P (δ q-end c)) →
        ∀ {q-end} →
          SnocDFA[ q-start →* q-end ] ⊢ P q-end
      elimSnocDFA P nil-case snoc-case (nil x) = nil-case x
      elimSnocDFA P nil-case snoc-case (snoc q-end c x) =
        snoc-case ((x .fst) , ((elimSnocDFA P nil-case snoc-case (x .snd .fst)) , (x .snd .snd)))

    DFATrace→SnocDFATrace : ∀ q-start q-end → DFA[ q-start →* q-end ] ⊢ SnocDFA[ q-start →* q-end ]
    DFATrace→SnocDFATrace q-start q-end =
      elimDFA q-end
        (λ q-start → SnocDFA[ q-start →* q-end ])
        nil
        (λ {q-start'} {c} →
          -⊗-elim {g = literal c} {h = SnocDFATrace (δ q-start' c) q-end}
           {k = SnocDFA[ q-start'  →* q-end ]} {l = literal c}
           (elimSnocDFA (δ q-start' c)
             (λ q-end' → literal c -⊗ SnocDFA[ q-start' →* q-end' ])
             (-⊗-intro {g = literal c} {h = ε-grammar}
               {k = SnocDFA[ q-start' →* (δ q-start' c) ]}
               (ε-extension-r {g = ε-grammar} {h = literal c}
                 {k = SnocDFA[ q-start' →* (δ q-start' c) ]}
                 (id {g = ε-grammar})
                 (ε-contraction-l {g = SnocDFA[ q-start' →* q-start' ]} {h = literal c}
                   {k = SnocDFA[ q-start' →* (δ q-start' c) ]}
                   nil
                   (snoc q-start' c)))
              )
             (λ {q-end'} {c'} →
               -⊗-intro {g = literal c}
                {h = (literal c -⊗ SnocDFATrace q-start' q-end') ⊗ literal c'}
                {k = SnocDFATrace q-start' (δ q-end' c')}
                (
                (⊗-elim
                  {g =
                   literal c ⊗
                   ((literal c -⊗ SnocDFA[ q-start' →* q-end' ]) ⊗ literal c')}
                  {h = literal c ⊗ (literal c -⊗ SnocDFA[ q-start' →* q-end' ])}
                  {k = literal c'}
                  {l = SnocDFA[ q-start' →* δ q-end' c' ]}
                  (⊗-assoc-inv {g = literal c}
                    {h = literal c -⊗ SnocDFATrace q-start' q-end'} {k = literal c'}
                    {l =
                     (literal c ⊗ (literal c -⊗ SnocDFATrace q-start' q-end')) ⊗
                     literal c'}
                    (id {g = ((literal c ⊗ (literal c -⊗ SnocDFATrace q-start' q-end')) ⊗ literal c')}))
                  (trans {g = (literal c ⊗ (literal c -⊗ SnocDFA[ q-start' →* q-end' ])) ⊗ literal c'}
                     {h = SnocDFA[ q-start' →* q-end' ] ⊗ literal c'} {k = SnocDFA[ q-start' →* δ q-end' c' ]}
                       (⊗-intro {g = literal c ⊗ (literal c -⊗ SnocDFA[ q-start' →* q-end' ])}
                         {h = SnocDFA[ q-start' →* q-end' ]}
                         {k = literal c'} {l = literal c'}
                         (-⊗-elim {g = literal c} {h = literal c -⊗ SnocDFA[ q-start' →* q-end' ]}
                           {k = SnocDFA[ q-start' →* q-end' ]} {l = literal c}
                           (id {g = literal c -⊗ SnocDFA[ q-start' →* q-end' ]})
                           (id {g = literal c}))
                         (id {g = literal c'}))
                       (snoc q-end' c'))
                  ))

              )
            )
           (id {g = literal c})
        )

    -- extendTrace' : ∀ {q : Q .fst} → (c : Σ₀) →
    --   Term ((TraceFrom q) ⊗ (literal c)) (TraceFrom q)
    -- extendTrace' {q} c (s , Σtr , lit) =
    --   let (q' , tr) = Σtr in
    --   (δ q' c) ,
    --   help (s , (tr , lit))

    --   where
    --   help : ∀ {q q-end} → Term (DFA[ q →* q-end ] ⊗ literal c) (DFA[ q →* (δ q-end c) ])
    --   help {q}{q-end} =
    --     {!!}
        -- ⊗--elim {g = DFA[ q →* q-end ]} {h = literal c} {k = DFA[ q →* (δ q-end c) ]} {l = literal c}
          -- (elimDFA q-end
          -- (λ q → DFA[ q →* (δ q-end c) ] ⊗- literal c)
          --   (λ {q-end} →
          --     ⊗--intro
          --       {g = ε-grammar} {h = literal c}
          --       {k = DFA[ q-end →* (δ q-end c) ]}
          --     (ε-extension-l {g = ε-grammar} {h = literal c} {k = DFA[ q-end →* (δ q-end c) ]}
          --       (id {ε-grammar})
          --       (ε-contraction-r {g = DFA[ (δ q-end c) →* (δ q-end c) ]} {h = literal c} {k = DFA[ q-end →* (δ q-end c) ]}
          --         {!!}
          --         {!!}
          --       )
          --     )
          --   )
          --   (λ {q}{q-end}{c'} →
          --     ⊗--intro
          --       {g = literal c' ⊗ (DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c)}
          --       {h = literal c} {k = DFA[ q →* (δ q-end c) ]}
          --       (trans
          --         {g = (literal c' ⊗ (DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c)) ⊗ literal c}
          --         {h = literal c' ⊗ DFA[ (δ q c') →* (δ q-end c) ]}
          --         {k = DFA[ q →* (δ q-end c) ]}
          --         (⊗-assoc
          --          {g = literal c'}
          --          {h = DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c}
          --          {k = literal c}
          --          {l = literal c' ⊗ DFA[ (δ q c') →* (δ q-end c) ]}
          --         (⊗-intro
          --           {g = literal c'} {h = literal c'}
          --           {k = (DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c) ⊗ literal c}
          --           {l = DFA[ (δ q c') →* (δ q-end c) ]}
          --           (id {literal c'})
          --           (⊗--elim
          --             {g = DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c}
          --             {h = literal c}
          --             {k = DFA[ (δ q c') →* (δ q-end c) ]}
          --             {l = literal c}
          --             (id {DFA[ (δ q c') →* (δ q-end c) ] ⊗- literal c})
          --             (id {literal c})))
          --          )
          --         (cons c'))
          --       )
          --   {q} {q-end})
          -- (id {literal c})

-- -- --     StringOfTrace : ∀ q q' → Term (DFATrace q q') (KL* ⊕Σ₀)
-- -- --     StringOfTrace q q' =
-- -- --       elimDFATrace
-- -- --         (λ _ _ → KL* ⊕Σ₀)
-- -- --         nil
-- -- --         (λ {q}{q'}{c} (s , lit , p) →
-- -- --           cons (s , ((c , lit) , p)))






--   open DFA

--   module _ (D : DFA) where
--     h = LinΣ[ q ∈ D .Q .fst ]
--         (DFATrace D (D .init) q
--           & (acc? D q ⊕ rej? D q))

--     checkAcc :
--       Term (TraceFrom D (D .init)) h
--     checkAcc (q , tr) =
--       q ,
--       &-intro
--         {g = DFATrace D (D .init) q}
--         {h = DFATrace D (D .init) q}
--         {k = acc? D q ⊕ rej? D q}
--         (id {DFATrace D (D .init) q})
--         (DecProp-grammar'-intro
--          (D .isAcc q)
--          {g = DFATrace D (D .init) q}
--         )
--         tr

--     run : Term (KL* ⊕Σ₀) h
--     run =
--       trans
--         {g = KL* ⊕Σ₀}
--         {h = TraceFrom D (D .init)}
--         {k = h}
--         (foldKL*l
--           {g = ⊕Σ₀}
--           {h = TraceFrom D (D .init)}
--           (λ x →
--             D .init ,
--             nil refl x
--           )
--           (λ (s , tr , c , lit) →
--             extendTrace' D {D .init} c (s , (tr , lit))
--           ))
--         checkAcc

--     decideDFA : String → Bool
--     decideDFA w =
--       Cubical.Data.Sum.rec
--         (λ _ → true)
--         (λ _ → false)
--         ((run (String→KL* w)) .snd .snd)

-- module examples where
--   -- examples are over alphabet drawn from Fin 2
--   -- characters are fzero and (fsuc fzero)
--   open DFADefs ℓ-zero (Fin 2 , isFinSetFin)
--   open GrammarDefs ℓ-zero (Fin 2 , isFinSetFin)
--   open StringDefs ℓ-zero (Fin 2 , isFinSetFin)

--   open DFA

--   D : DFA
--   Q D = (Fin 3) , isFinSetFin
--   init D = inl _
--   isAcc D x =
--     ((x ≡ fzero) , isSetFin x fzero) ,
--     discreteFin x fzero
--   δ D fzero fzero = fromℕ 0
--   δ D fzero (fsuc fzero) = fromℕ 1
--   δ D (fsuc fzero) fzero = fromℕ 2
--   δ D (fsuc fzero) (fsuc fzero) = fromℕ 0
--   δ D (fsuc (fsuc fzero)) fzero = fromℕ 1
--   δ D (fsuc (fsuc fzero)) (fsuc fzero) = fromℕ 2

--   w : String
--   w = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fzero ∷ []

--   w' : String
--   w' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

--   w'' : String
--   w'' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

--   ex1 : decideDFA D w ≡ true
--   ex1 = refl

--   ex2 : decideDFA D w' ≡ true
--   ex2 = refl

--   ex3 : decideDFA D w'' ≡ false
--   ex3 = refl

--   ex4 : decideDFA D [] ≡ true
--   ex4 = refl


--  {--       0
--  -- 0  --------> 1
--  --    <--------
--  --        0
--  -- and self loops for 1. state 1 is acc
--  --
--  --}
--   D' : DFA
--   Q D' = (Fin 2) , isFinSetFin
--   init D' = inl _
--   isAcc D' x =
--     ((x ≡ fsuc fzero) , isSetFin x (fsuc fzero)) ,
--     discreteFin x (fsuc fzero)
--   δ D' fzero fzero = fromℕ 1
--   δ D' fzero (fsuc fzero) = fromℕ 0
--   δ D' (fsuc fzero) fzero = fromℕ 0
--   δ D' (fsuc fzero) (fsuc fzero) = fromℕ 1

--   s : String
--   s = fsuc fzero ∷ fzero ∷ []

--   ex5 : decideDFA D' s ≡ true
--   ex5 = refl
