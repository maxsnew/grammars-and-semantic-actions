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

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    acc? : Q .fst → Grammar
    acc? q = DecProp-grammar' (isAcc q)

    rej? : Q .fst → Grammar
    rej? q = DecProp-grammar' (negateDecProp (isAcc q))

    data DFATrace (q : Q .fst) (q-end : Q .fst) : String → Type ℓ where
      nil : (q ≡ q-end) → Term ε-grammar (DFATrace q q-end)
      cons : ∀ c →
        Term
          (literal c ⊗ DFATrace (δ q c) q-end) (DFATrace q q-end)

    elimDFATrace :
      (P : ∀ q q' → Grammar) →
      (nil-case : ∀ {q} → Term ε-grammar (P q q)) →
      (cons-case : ∀ {q}{q'}{c} → Term (literal c ⊗ P (δ q c) q') (P q q')) →
      ∀ {q q'} → Term (DFATrace q q') (P q q')
    elimDFATrace P nil-case cons-case {q}{q'} (nil x y) =
      transport (cong₂ (λ a b → P q a b) x (sym y)) (nil-case refl)
    elimDFATrace P nil-case cons-case (cons c x) =
      cons-case
        ((([ c ] , (x .fst .fst .snd)) ,
        (x .fst .snd ∙ cong (λ a → a ++ x .fst .fst .snd) (x .snd .fst))) ,
        (refl , (elimDFATrace P nil-case cons-case (x .snd .snd))))

    TraceFrom : (Q .fst) → Grammar
    TraceFrom q = LinΣ[ q' ∈ Q .fst ] DFATrace q q'

    extendTrace' : ∀ {q : Q .fst} → (c : Σ₀) →
      Term ((TraceFrom q) ⊗ (literal c)) (TraceFrom q)
    extendTrace' {q} c (s , Σtr , lit) =
      let (q' , tr) = Σtr in
      (δ q' c) ,
      help (s , (tr , lit))

      where
      help : ∀ {q q'} → Term (DFATrace q q' ⊗ literal c) (DFATrace q (δ q' c))
      help {q}{q'} =
        ⊗--elim {g = DFATrace q q'} {h = literal c} {k = DFATrace q (δ q' c)} {l = literal c}
          (elimDFATrace
          (λ q q' → DFATrace q (δ q' c) ⊗- literal c)
            (λ {q'} →
              ⊗--intro
                {g = ε-grammar} {h = literal c}
                {k = DFATrace q' (δ q' c)}
              (ε-extension-l {g = ε-grammar} {h = literal c} {k = DFATrace q' (δ q' c)}
                (id {ε-grammar})
                (ε-contraction-r {g = DFATrace (δ q' c) (δ q' c)} {h = literal c} {k = DFATrace q' (δ q' c)}
                  (nil refl)
                  (cons c)
                )
              )
            )
            (λ {q}{q'}{c'} →
              ⊗--intro
                {g = literal c' ⊗ ((DFATrace (δ q c') (δ q' c)) ⊗- literal c)}
                {h = literal c} {k = DFATrace q (δ q' c)}
                (trans
                  {g = (literal c' ⊗ ((DFATrace (δ q c') (δ q' c)) ⊗- literal c)) ⊗ literal c}
                  {h = literal c' ⊗ DFATrace (δ q c') (δ q' c)}
                  {k = DFATrace q (δ q' c)}
                  (⊗-assoc
                   {g = literal c'}
                   {h = DFATrace (δ q c') (δ q' c) ⊗- literal c}
                   {k = literal c}
                   {l = literal c' ⊗ DFATrace (δ q c') (δ q' c)}
                  (⊗-intro
                    {g = literal c'} {h = literal c'}
                    {k = (DFATrace (δ q c') (δ q' c) ⊗- literal c) ⊗ literal c}
                    {l = DFATrace (δ q c') (δ q' c)}
                    (id {literal c'})
                    (⊗--elim
                      {g = DFATrace (δ q c') (δ q' c) ⊗- literal c}
                      {h = literal c}
                      {k = DFATrace (δ q c') (δ q' c)}
                      {l = literal c}
                      (id {DFATrace (δ q c') (δ q' c) ⊗- literal c})
                      (id {literal c})))
                   )
                  (cons c'))
                )
            {q} {q'})
          (id {literal c})

    Parses : Grammar
    Parses = LinΣ[ q ∈ Q .fst ] (DFATrace init q & acc? q)

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ

  open DFA

  module _ (D : DFA) where
    h = LinΣ[ q ∈ D .Q .fst ]
        (DFATrace D (D .init) q
          & (acc? D q ⊕ rej? D q))

    checkAcc :
      Term (TraceFrom D (D .init)) h
    checkAcc (q , tr) =
      q ,
      &-intro
        {g = DFATrace D (D .init) q}
        {h = DFATrace D (D .init) q}
        {k = acc? D q ⊕ rej? D q}
        (id {DFATrace D (D .init) q})
        (DecProp-grammar'-intro
         (D .isAcc q)
         {g = DFATrace D (D .init) q}
        )
        tr

    run : Term (KL* ⊕Σ₀) h
    run =
      trans
        {g = KL* ⊕Σ₀}
        {h = TraceFrom D (D .init)}
        {k = h}
        (foldKL*l
          {g = ⊕Σ₀}
          {h = TraceFrom D (D .init)}
          (λ x →
            D .init ,
            nil refl x
          )
          (λ (s , tr , c , lit) →
            extendTrace' D {D .init} c (s , (tr , lit))
          ))
        checkAcc

    decideDFA : String → Bool
    decideDFA w =
      Cubical.Data.Sum.rec
        (λ _ → true)
        (λ _ → false)
        ((run (String→KL* w)) .snd .snd)

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

  ex1 : decideDFA D w ≡ true
  ex1 = refl

  ex2 : decideDFA D w' ≡ true
  ex2 = refl

  ex3 : decideDFA D w'' ≡ false
  ex3 = refl

  ex4 : decideDFA D [] ≡ true
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

  ex5 : decideDFA D' s ≡ true
  ex5 = refl
