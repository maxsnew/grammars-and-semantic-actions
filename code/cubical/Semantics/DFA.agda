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
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module DFADefs ℓD ((Σ₀ , isFinSetΣ₀) : FinSet ℓ-zero) where
  record DFA : Type (ℓ-suc ℓD) where
    field
      Q : FinSet ℓD
      init : Q .fst
      isAcc : Q .fst → DecProp ℓD
      δ : Q .fst → Σ₀ → Q .fst

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    Accepting : Type ℓD
    Accepting = Σ[ q ∈ Q .fst ] isAcc q .fst .fst

    acc? : Q .fst → Grammar {Σ₀} ℓD
    acc? q = DecProp-grammar' {ℓG = ℓD} (isAcc q)

    rej? : Q .fst → Grammar {Σ₀} ℓD
    rej? q = DecProp-grammar' {ℓG = ℓD} (negateDecProp (isAcc q))

    module _ (q-end : Q .fst) where
      data DFATrace : Q .fst → Grammar ℓD where
        nil : ε-grammar ⊢ DFATrace q-end
        cons : ∀ q-start c →
             literal c ⊗ DFATrace (δ q-start c) ⊢ DFATrace q-start

      module _
        (P : ∀ q-start → Grammar ℓD)
        (nil-case : ε-grammar ⊢ P q-end)
        (cons-case : ∀ {q-start}{c} →
          literal c ⊗ P (δ q-start c) ⊢ (P q-start))
        where

        elimDFA :
          ∀ {q-start} →
            DFATrace q-start ⊢ P q-start
        elimDFA (nil x) = nil-case x
        elimDFA (cons q-start' c x) =
          cons-case (x .fst , x .snd .fst , (elimDFA (x .snd .snd)))

        elimDFA-unique :
          (e : (∀ {q} → DFATrace q ⊢ P q)) →
          (e-alg-nil : Term≡ {Σ₀} {g = ε-grammar}
            nil-case
            (trans
              {g = ε-grammar}
              {h = DFATrace q-end}
              {k = P q-end}
              nil
              e)
            ) →
          (e-alg-cons : ∀ q-start c → Term≡ {Σ₀} {g = literal c ⊗ DFATrace (δ q-start c)}
            (trans {g = literal c ⊗ DFATrace (δ q-start c)}
              {h = literal c ⊗ P (δ q-start c)}
              {k = P q-start}
              (cut {g = DFATrace (δ q-start c)} {h = P (δ q-start c)} (literal c ⊗r var) e)
              (cons-case {q-start} {c}))
            (trans {g = literal c ⊗ DFATrace (δ q-start c)}
              {h = DFATrace q-start}
              {k = P q-start}
              (cons q-start c)
              e
            )
          ) →
          ∀ {q-start} → Term≡ {g = DFATrace q-start} elimDFA e
        elimDFA-unique e e-alg-nil e-alg-cons (nil x) = e-alg-nil x
        elimDFA-unique e e-alg-nil e-alg-cons (cons q-start c (s , lit , x)) =
          let eq-on-x = elimDFA-unique e e-alg-nil e-alg-cons x in
            cong cons-case (ΣPathP (refl , (ΣPathP (refl , eq-on-x)))) ∙
            e-alg-cons q-start c (s , lit , x)

    DFATrace-syntax : Q .fst → Q .fst → Grammar ℓD
    DFATrace-syntax q-end q-start = DFATrace q-end q-start
    syntax DFATrace-syntax q-end q-start = DFA[ q-start →* q-end ]

    module _ (q-start : Q .fst) where
      data SnocDFATrace : (q-end : Q .fst) → Grammar ℓD where
        nil : ε-grammar ⊢ SnocDFATrace q-start
        snoc : ∀ q-end c →
          SnocDFATrace q-end ⊗ literal c ⊢ SnocDFATrace (δ q-end c)

      module _
        (P : ∀ q-end → Grammar ℓD)
        (nil-case : ε-grammar  ⊢ P q-start)
        (snoc-case : ∀ {q-end}{c} →
          P q-end ⊗ literal c ⊢ P (δ q-end c))
        where

        elimSnocDFA :
          ∀ {q-end} →
            SnocDFATrace q-end ⊢ P q-end
        elimSnocDFA (nil x) = nil-case x
        elimSnocDFA (snoc q-end c x) =
          snoc-case ((x .fst) , ((elimSnocDFA (x .snd .fst)) , (x .snd .snd)))

        elimSnocDFA-unique :
          (e : (∀ {q} → SnocDFATrace q ⊢ P q)) →
          (e-alg-nil : Term≡ {Σ₀} {g = ε-grammar}
            nil-case
            (trans
              {g = ε-grammar}
              {h = SnocDFATrace q-start}
              {k = P q-start}
              nil
              e)
          ) →
          (e-alg-snoc : ∀ q-end c →
            Term≡ {Σ₀} {g = SnocDFATrace q-end ⊗ literal c}
              (trans {g = SnocDFATrace q-end ⊗ literal c}
                {h = P q-end ⊗ literal c} {k = P (δ q-end c)}
                (cut {g = SnocDFATrace q-end} {h = P q-end} (var ⊗l literal c) e)
                snoc-case)
              (trans {g = SnocDFATrace q-end ⊗ literal c}
                {h = SnocDFATrace (δ q-end c)} {k = P (δ q-end c)}
                (snoc q-end c)
                e)) →
          ∀ {q-end} → Term≡ {g = SnocDFATrace q-end} elimSnocDFA e
        elimSnocDFA-unique e e-alg-nil e-alg-snoc (nil x) = e-alg-nil x
        elimSnocDFA-unique e e-alg-nil e-alg-snoc (snoc q-end c x) =
          cong snoc-case (ΣPathP (refl ,
            (ΣPathP ((elimSnocDFA-unique e e-alg-nil e-alg-snoc (x .snd .fst)) , refl)))) ∙
          e-alg-snoc q-end c x

    SnocDFATrace-syntax : Q .fst → Q .fst → Grammar ℓD
    SnocDFATrace-syntax q-start q-end = SnocDFATrace q-start q-end
    syntax SnocDFATrace-syntax q-start q-end = SnocDFA[ q-start →* q-end ]

    module _ (q-start q-end : Q .fst) where
      DFATrace→SnocDFATrace : DFA[ q-start →* q-end ] ⊢ SnocDFA[ q-start →* q-end ]
      DFATrace→SnocDFATrace =
        elimDFA q-end
          (λ q-start → SnocDFA[ q-start →* q-end ])
          nil
          (λ {q-start'} {c} →
            -⊗-elim {g = SnocDFATrace (δ q-start' c) q-end} {h = literal c}
             {k = SnocDFATrace-syntax q-start' q-end} {l = literal c}
              (elimSnocDFA (δ q-start' c)
                (λ q-end' → literal c -⊗ SnocDFA[ q-start' →* q-end' ])
                (-⊗-intro {g = literal c} {h = ε-grammar}
                  {k = SnocDFA[ q-start' →* δ q-start' c ]}
                  (ε-extension-r {g = ε-grammar} {h = literal c}
                    {k = SnocDFA[ q-start' →* δ q-start' c ]}
                    (id {g = ε-grammar})
                    (ε-contraction-l {g = SnocDFA[ q-start' →* q-start' ]}
                      {h = literal c}
                      {k = SnocDFA[ q-start' →* δ q-start' c ]}
                      nil
                      (snoc q-start' c))))
                (λ {q-end'} {c'} →
                  -⊗-intro {g = literal c}
                   {h = (literal c -⊗ SnocDFATrace q-start' q-end') ⊗ literal c'}
                   {k = SnocDFATrace q-start' (δ q-end' c')}
                   (⊗-elim
                     {g =
                      literal c ⊗
                      (literal c -⊗ SnocDFATrace-syntax q-start' q-end') ⊗ literal c'}
                     {h =
                      literal c ⊗ (literal c -⊗ SnocDFATrace-syntax q-start' q-end')}
                     {k = literal c'} {l = SnocDFATrace-syntax q-start' (δ q-end' c')}
                     (⊗-assoc-inv {g = literal c}
                       {h = literal c -⊗ SnocDFATrace q-start' q-end'} {k = literal c'}
                       {l =
                        (literal c ⊗ (literal c -⊗ SnocDFATrace q-start' q-end')) ⊗
                        literal c'}
                       (id {g = ((literal c ⊗ (literal c -⊗ SnocDFATrace q-start' q-end')) ⊗ literal c')}))
                     (trans
                       {g =
                        (literal c ⊗ (literal c -⊗ SnocDFATrace-syntax q-start' q-end')) ⊗
                        literal c'}
                       {h = SnocDFATrace-syntax q-start' q-end' ⊗ literal c'}
                       {k = SnocDFATrace-syntax q-start' (δ q-end' c')}
                         (cut
                           {g =
                            literal c ⊗ (literal c -⊗ SnocDFATrace-syntax q-start' q-end')}
                           {h = SnocDFATrace-syntax q-start' q-end'} (var ⊗l literal c')
                           (-⊗-elim {g = literal c -⊗ SnocDFATrace-syntax q-start' q-end'}
                             {h = literal c} {k = SnocDFATrace-syntax q-start' q-end'}
                             {l = literal c}
                               (id {g = literal c -⊗ SnocDFA[ q-start' →* q-end' ]})
                               (id {g = literal c})))
                         (snoc q-end' c')))))
              (id {g = literal c}))

      SnocDFATrace→DFATrace : ∀ q-start q-end → SnocDFA[ q-start →* q-end ] ⊢ DFA[ q-start →* q-end ]
      SnocDFATrace→DFATrace q-start q-end =
        elimSnocDFA q-start
          (λ q-end → DFA[ q-start →* q-end ])
          nil
          (λ {q-end'} {c} →
            ⊗--elim {g = DFA[ q-start →* q-end' ]}
              {h = DFA[ q-start →* δ q-end' c ]} {k = literal c} {l = literal c}
              (elimDFA q-end'
                (λ q-start' → DFA[ q-start' →* δ q-end' c ] ⊗- literal c)
                (⊗--intro {g = ε-grammar} {h = literal c}
                  {k = DFATrace-syntax (δ q-end' c) q-end'}
                  (ε-extension-l {g = ε-grammar} {h = literal c}
                    {k = DFATrace-syntax (δ q-end' c) q-end'}
                    (id {g = ε-grammar})
                    (ε-contraction-r {g = DFATrace-syntax (δ q-end' c) (δ q-end' c)}
                      {h = literal c} {k = DFATrace-syntax (δ q-end' c) q-end'}
                        nil
                        (cons q-end' c))))
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
                          (⊗--elim
                            {g = DFATrace-syntax (δ q-end' c) (δ q-start' c') ⊗- literal c}
                            {h = DFATrace-syntax (δ q-end' c) (δ q-start' c')} {k = literal c}
                            {l = literal c}
                            (id {g = DFATrace-syntax (δ q-end' c) (δ q-start' c') ⊗- literal c} )
                            (id {g = literal c}))
                          )
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
      TraceFrom : Grammar ℓD
      TraceFrom = LinearΣ (λ (q-end : Q .fst) → DFA[ q-start →* q-end ])

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
            DFATraceAppendLiteral q-start q-end (s , (trace , lit)))

      TraceWithAcceptanceFrom : Grammar ℓD
      TraceWithAcceptanceFrom =
        LinearΣ
          (λ (q-end : Q .fst) →
             (DFA[ q-start →* q-end ] & (acc? q-end ⊕ rej? q-end)))

      checkAccept : TraceFrom ⊢ TraceWithAcceptanceFrom
      checkAccept (q-end , trace) =
        q-end ,
        &-intro {g = DFA[ q-start →* q-end ]} {h = DFA[ q-start →* q-end ]} {k = acc? q-end ⊕ rej? q-end}
          (id {g = DFA[ q-start →* q-end ]})
          (DecProp-grammar'-intro (isAcc q-end)
            {g = DFA[ q-start →* q-end ] })
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

  w : String {Σ₀ = Fin 2}
  w = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fzero ∷ []

  w' : String {Σ₀ = Fin 2}
  w' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

  w'' : String {Σ₀ = Fin 2}
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

  s : String {Σ₀ = Fin 2}
  s = fsuc fzero ∷ fzero ∷ []

  ex5 : DecideDFA D' s ≡ true
  ex5 = refl
