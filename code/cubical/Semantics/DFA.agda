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
open import Cubical.Data.Sum as Sum
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

    module _ (q-end : Q .fst) where
      data DFATrace : Q .fst → String → Type ℓ where
        nil : ε-grammar ⊢ DFATrace q-end
        cons : ∀ q-start c →
             literal c ⊗ DFATrace (δ q-start c) ⊢ DFATrace q-start

      elimDFA :
        (P : ∀ q-start → Grammar) →
        (nil-case : ε-grammar ⊢ P q-end) →
        (cons-case : ∀ {q-start}{c} →
          literal c ⊗ P (δ q-start c) ⊢ (P q-start)) →
        ∀ {q-start} →
          DFATrace q-start ⊢ P q-start
      elimDFA P nil-case cons-case (nil x) = nil-case x
      elimDFA P nil-case cons-case (cons q-start c x) =
        cons-case (x .fst , x .snd .fst , (elimDFA P nil-case cons-case (x .snd .snd)))

    DFATrace-syntax : Q .fst → Q .fst → String → Type ℓ
    DFATrace-syntax q-end q-start = DFATrace q-end q-start
    syntax DFATrace-syntax q-end q-start = DFA[ q-start →* q-end ]


    module _ (q-start : Q .fst) where
      data SnocDFATrace : (q-end : Q .fst) → String → Type ℓ where
        nil : ε-grammar ⊢ SnocDFATrace q-start
        snoc : ∀ q-end c →
          SnocDFATrace q-end ⊗ literal c ⊢ SnocDFATrace (δ q-end c)

      elimSnocDFA :
        (P : ∀ q-end → Grammar) →
        (nil-case : ε-grammar ⊢ P q-start) →
        (snoc-case : ∀ {q-end}{c} →
          P q-end ⊗ literal c ⊢ P (δ q-end c)) →
        ∀ {q-end} →
          SnocDFATrace q-end ⊢ P q-end
      elimSnocDFA P nil-case snoc-case (nil x) = nil-case x
      elimSnocDFA P nil-case snoc-case (snoc q-end c x) =
        snoc-case ((x .fst) , ((elimSnocDFA P nil-case snoc-case (x .snd .fst)) , (x .snd .snd)))

    SnocDFATrace-syntax : Q .fst → Q .fst → String → Type ℓ
    SnocDFATrace-syntax q-start q-end = SnocDFATrace q-start q-end
    syntax SnocDFATrace-syntax q-start q-end = SnocDFA[ q-start →* q-end ]

    module _ (q-start q-end : Q .fst) where
      DFATrace→SnocDFATrace : DFA[ q-start →* q-end ] ⊢ SnocDFA[ q-start →* q-end ]
      DFATrace→SnocDFATrace =
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

      SnocDFATrace→DFATrace : ∀ q-start q-end → SnocDFA[ q-start →* q-end ] ⊢ DFA[ q-start →* q-end ]
      SnocDFATrace→DFATrace q-start q-end =
        elimSnocDFA q-start
          (λ q-end → DFA[ q-start →* q-end ])
          nil
          (λ {q-end'} {c} →
            ⊗--elim {g = DFA[ q-start →* q-end' ]} {h = literal c}
              {k = DFA[ q-start →* δ q-end' c ]} {l = literal c}
              (elimDFA q-end'
                (λ q-start' → DFA[ q-start' →* δ q-end' c ] ⊗- literal c)
                (⊗--intro {g = ε-grammar} {h = literal c} {k = DFA[ q-end' →* δ q-end' c ]}
                   (ε-extension-l {g = ε-grammar} {h = literal c} {k = DFA[ q-end' →* δ q-end' c ]}
                     (id {g = ε-grammar})
                     (ε-contraction-r {g = DFA[ δ q-end' c →* δ q-end' c ]} {h = literal c}
                       {k = DFA[ q-end' →* δ q-end' c ]}
                       nil
                       (cons q-end' c))
                    )
                )
                (λ {q-start'} {c'} →
                  ⊗--intro {g = literal c' ⊗ (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c)}
                    {h = literal c} {k = DFA[ q-start' →* δ q-end' c ]}
                    (⊗-elim {g = (literal c' ⊗ (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c)) ⊗ literal c}
                      {h = literal c'}
                      {k = (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c) ⊗ literal c}
                      {l = DFA[ q-start' →* δ q-end' c ]}
                      (⊗-assoc {g = literal c'} {h = DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c}
                        {k = literal c}
                        {l = (literal c' ⊗ (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c) ⊗ literal c)}
                        (id {g = (literal c' ⊗ (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c) ⊗ literal c)}))
                      (trans {g = (literal c' ⊗ (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c) ⊗ literal c)}
                        {h = literal c' ⊗ DFA[ δ q-start' c' →* δ q-end' c ]}
                        {k = DFA[ q-start' →* δ q-end' c ]}
                        (⊗-intro {g = literal c'} {h = literal c'}
                          {k = (DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c) ⊗ literal c}
                          {l = DFA[ δ q-start' c' →* δ q-end' c ]}
                          (id {g = literal c'})
                          (⊗--elim {g = DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c}
                            {h = literal c}
                            {k = DFA[ δ q-start' c' →* δ q-end' c ]}
                            {l = literal c}
                            (id {g = DFA[ δ q-start' c' →* δ q-end' c ] ⊗- literal c })
                            (id {g = literal c})))
                        (cons q-start' c')))))
              (id {g = literal c})
          )

      DFATraceAppendLiteral : ∀ {c} →
        DFA[ q-start →* q-end ] ⊗ literal c ⊢ DFA[ q-start →* (δ q-end c) ]
      DFATraceAppendLiteral {c} =
        trans {g = DFA[ q-start →* q-end ] ⊗ literal c}
          {h = SnocDFA[ q-start →* δ q-end c ]}
          {k = DFA[ q-start →* δ q-end c ]}
          (⊗-trans-l {g = DFA[ q-start →* q-end ]}
            {h = SnocDFA[ q-start →* q-end ]} {k = literal c}
            {l = SnocDFA[ q-start →* δ q-end c ]}
            DFATrace→SnocDFATrace
            (snoc q-end c))
          (SnocDFATrace→DFATrace q-start (δ q-end c))

    module _ (q-start : Q .fst) where
      TraceFrom : Grammar
      TraceFrom = LinΣ[ q-end ∈ Q .fst ] DFA[ q-start →* q-end ]

      ExtendTraceFromByLiteral : ∀ (c : Σ₀) →
        TraceFrom ⊗ (literal c) ⊢ TraceFrom
      ExtendTraceFromByLiteral c (s , Σtr , lit) =
        let (q-end , tr) = Σtr in
        (δ q-end c) ,
        DFATraceAppendLiteral q-start q-end (s , (tr , lit))

      RunFromState : KL* ⊕Σ₀ ⊢ TraceFrom
      RunFromState =
        foldKL*l {g = ⊕Σ₀} {h = TraceFrom}
          (λ pε → q-start , (nil pε))
          (λ (s , (q-end , trace) , c , lit) →
            δ q-end c ,
            DFATraceAppendLiteral q-start q-end
              (s , (trace , lit)))

      TraceWithAcceptanceFrom : Grammar
      TraceWithAcceptanceFrom =
        LinΣ[ q-end ∈ Q .fst ] (DFA[ q-start →* q-end ] & (acc? q-end ⊕ rej? q-end))

      checkAccept : TraceFrom ⊢ TraceWithAcceptanceFrom
      checkAccept (q-end , trace) =
        q-end ,
        &-intro {g = DFA[ q-start →* q-end ]} {h = DFA[ q-start →* q-end ]} {k = acc? q-end ⊕ rej? q-end}
          (id {g = DFA[ q-start →* q-end ]})
          (DecProp-grammar'-intro (isAcc q-end) {g = DFA[ q-start →* q-end ]})
          trace

      RunFromStateWithAcceptance : KL* ⊕Σ₀ ⊢ TraceWithAcceptanceFrom
      RunFromStateWithAcceptance =
        trans {g = KL* ⊕Σ₀} {h = TraceFrom} {k = TraceWithAcceptanceFrom}
          RunFromState checkAccept

      DecideFromState : String → Bool
      DecideFromState w =
        let the-trace = RunFromStateWithAcceptance (String→KL* w) in
        Sum.rec (λ _ → true) (λ _ → false) (the-trace .snd .snd)

    DecideDFA : String → Bool
    DecideDFA = DecideFromState init

module examples where
  -- examples are over alphabet drawn from Fin 2
  -- characters are fzero and (fsuc fzero)
  open DFADefs ℓ-zero (Fin 2 , isFinSetFin)
  open GrammarDefs ℓ-zero (Fin 2 , isFinSetFin)
  open StringDefs ℓ-zero (Fin 2 , isFinSetFin)

  open DFA

  D : DFA
  Q D = (Fin 3) , isFinSetFin
  init D = inl _
  isAcc D x =
    ((x ≡ fzero) , isSetFin x fzero) ,
    discreteFin x fzero
  δ D fzero fzero = fromℕ 0
  δ D fzero (fsuc fzero) = fromℕ 1
  δ D (fsuc fzero) fzero = fromℕ 2
  δ D (fsuc fzero) (fsuc fzero) = fromℕ 0
  δ D (fsuc (fsuc fzero)) fzero = fromℕ 1
  δ D (fsuc (fsuc fzero)) (fsuc fzero) = fromℕ 2

  w : String
  w = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fzero ∷ []

  w' : String
  w' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

  w'' : String
  w'' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

  ex1 : DecideDFA D w ≡ true
  ex1 = refl

  ex2 : DecideDFA D w' ≡ true
  ex2 = refl

  ex3 : DecideDFA D w'' ≡ false
  ex3 = refl

  ex4 : DecideDFA D [] ≡ true
  ex4 = refl


 {--       0
 -- 0  --------> 1
 --    <--------
 --        0
 -- and self loops for 1. state 1 is acc
 --
 --}
  D' : DFA
  Q D' = (Fin 2) , isFinSetFin
  init D' = inl _
  isAcc D' x =
    ((x ≡ fsuc fzero) , isSetFin x (fsuc fzero)) ,
    discreteFin x (fsuc fzero)
  δ D' fzero fzero = fromℕ 1
  δ D' fzero (fsuc fzero) = fromℕ 0
  δ D' (fsuc fzero) fzero = fromℕ 0
  δ D' (fsuc fzero) (fsuc fzero) = fromℕ 1

  s : String
  s = fsuc fzero ∷ fzero ∷ []

  ex5 : DecideDFA D' s ≡ true
  ex5 = refl
