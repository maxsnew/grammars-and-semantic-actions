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

open import Cubical.Data.List
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

private
  variable ℓ ℓ' : Level

module DFADefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀) public
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀) public

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
    acc? q = DecProp-grammar (isAcc q) ⊤-grammar ⊥-grammar

    rej? : Q .fst → Grammar
    rej? q = DecProp-grammar (negateDecProp (isAcc q)) ⊤-grammar ⊥-grammar

    data DFATrace (q : Q .fst) (q-end : Q .fst) : String → Type ℓ where
      nil : ParseTransformer ε-grammar (DFATrace q q-end)
      cons : ∀ c →
        ParseTransformer
          (literal c ⊗ DFATrace (δ q c) q-end) (DFATrace q q-end)

    -- This is the only sus helper function
    -- This adds to a trace in the wrong order, however this is definable
    -- in the paper type theory via the same principle as below
    extendTrace : ∀ {q q' : Q .fst} {w} → DFATrace q q' w → (c : Σ₀) →
      DFATrace q (δ q' c) (w ++ [ c ])
    extendTrace (nil x) c =
      cons c (((c ∷ [] , _) ,
        cong (λ a → a ++ [ c ]) x ∙ sym (cong (λ a → c ∷ a) x)) ,
          (refl , (nil x)))
    extendTrace {q}{q'} (cons c' x) c =
      cons c' (the-split , (refl , (extendTrace (x .snd .snd) c)))
      where
      the-split : Splitting (_ ++ [ c ])
      the-split = ([ c' ] , x .fst .fst .snd ++ [ c ]) ,
        (cong (λ a → a ++ [ c ]) (x .fst .snd) ∙
          (cong (λ a → (a ++ (x .fst .fst .snd)) ++ [ c ]) (x .snd .fst)))
          ∙ ++-assoc [ c' ] (x .fst .fst .snd) [ c ]

    Parses : Grammar
    Parses =
      LinΣ[ q ∈ Σ[ q' ∈ Q .fst ] isAcc q' .fst .fst ] DFATrace init (q .fst)

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ

  open DFA


  module _ (D : DFA) where
    ¬D : DFA
    ¬D = negate D

    trace→negationTrace : ∀ {q}{q'}{w} → DFATrace D q q' w → DFATrace ¬D q q' w
    trace→negationTrace (nil x) = nil x
    trace→negationTrace (cons c x) =
      cons c (x .fst , (x .snd .fst , (trace→negationTrace (x .snd .snd))))

    h =
      LinΣ[ q ∈ D .Q .fst ]
        (DFATrace D (D .init) q
          & (acc? D q ⊕ rej? D q))

    run' :
      ParseTransformer
        (KL* ⊕Σ₀)
        h
    run' p =
      fold*l
        ⊕Σ₀
        h
        mt-case
        cons-case
        p
      where

      mt-case : ParseTransformer ε-grammar h
      fst (mt-case p) = D .init
      fst (snd (mt-case p)) = nil p
      snd (snd (mt-case p)) =
        decRec
          (λ acc → inl (DecProp-grammar-yes (D .isAcc (D .init)) _ _ acc _ _))
          (λ ¬acc → inr (DecProp-grammar-yes
            (negateDecProp (D .isAcc (D .init)))
            _ _ ¬acc _ _))
          (D .isAcc (D .init) .snd)

      cons-case : ParseTransformer (h ⊗ ⊕Σ₀) h
      fst (cons-case p) = D .δ (p .snd .fst .fst) (p .snd .snd .fst)
      fst (snd (cons-case p)) = 
        transport
        (cong (λ a → DFATrace D _ _ a)
          (cong (λ a → p .fst .fst .fst ++ a)
            (sym (p .snd .snd .snd)) ∙ sym (p .fst .snd)))
        (extendTrace D (p .snd .fst .snd .fst) (p .snd .snd .fst))
      snd (snd (cons-case p)) =
        decRec
          (λ acc → inl (DecProp-grammar-yes (D .isAcc _) _ _ acc _ _))
          (λ ¬acc → inr (
            DecProp-grammar-yes (negateDecProp (D .isAcc _))
              _ _ ¬acc _ _))
          (D .isAcc (D .δ (p .snd .fst .fst) (p .snd .snd .fst)) .snd)

    toParse : ParseTransformer h (Parses D ⊕ Parses ¬D)
    toParse (a , b , inl x) =
      inl ((a , elimSimpleDecProp-grammar (D .isAcc _) _ x) , b)
    toParse (a , b , inr x) =
      inr ((a , elimSimpleDecProp-grammar (negateDecProp (D .isAcc _)) _ x) ,
        trace→negationTrace b)

    run : ParseTransformer (KL* ⊕Σ₀) (Parses D ⊕ Parses ¬D)
    run p = toParse (run' p)

    decideDFA : String → Bool
    decideDFA w =
      Cubical.Data.Sum.rec
        (λ _ → true)
        (λ _ → false)
        (run (String→KL* w))

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

  w : String
  w = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fzero ∷ []

  w' : String
  w' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

  w'' : String
  w'' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []


  p : Parses D w
  p =
    (fzero , refl) ,
    (cons fzero (stepLiteral
      (cons (fsuc fzero) (stepLiteral
        (cons (fsuc fzero) (stepLiteral
          (cons fzero (stepLiteral (nil refl)))))))))

  ex1 : decideDFA D w ≡ true
  ex1 = refl

  ex2 : decideDFA D w' ≡ true
  ex2 = refl

  ex3 : decideDFA D w'' ≡ false
  ex3 = refl

  ex4 : decideDFA D [] ≡ true
  ex4 = refl
