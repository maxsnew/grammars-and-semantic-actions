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
    acc? q = DecProp-grammar (isAcc q) ε-grammar ⊥-grammar

    data DFATrace (q : Q .fst) : String → Type ℓ where
      nil : ParseTransformer (acc? q) (DFATrace q)
      cons : ∀ c → ParseTransformer (literal c ⊗ DFATrace (δ q c)) (DFATrace q)

    Parses : String → Type ℓ
    Parses w = DFATrace init w

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ


  open DFA

  module _ (D : DFA) where
    acceptingState : ∀ q w → DFATrace D q w → D .Q .fst
    acceptingState q [] (nil x) = q
    acceptingState q [] (cons c x) =
      ⊥.rec (¬cons≡nil {!!})
      where
      x₁₁₁≡[] : x .fst .fst .fst ≡ []
      x₁₁₁≡[] = {!cons-inj₁  !}
    acceptingState q (c ∷ w) (nil x) =
      ⊥.rec {!!}
    acceptingState q (c ∷ w) (cons c' x) =
      decRec
        (λ c≡c' → acceptingState (D .δ q c') w
          (transport
            (cong (λ a → DFATrace D (D .δ q c') a)
              (sym (cons-inj₂ ((x .fst .snd) ∙
                cong (λ a → a ++ x .fst .fst .snd) (x .snd .fst)))))
            (x .snd .snd)))
        (λ ¬c≡c' → ⊥.rec {!x .snd .fst!})
        (DiscreteΣ₀ c c')
      where
      a : c ≡ c'
      a = {!x .snd !}
      -- TODO need to prove that literal c' ⊗ ... (c ∷ w) splits
      -- properly

    ¬D : DFA
    ¬D = negate D

    run :
      ParseTransformer
        (KL* ⊕Σ₀)
        ((LinΣ[ q ∈ (Σ[ q' ∈ D .Q .fst ] D .isAcc q' .fst .fst) ] {!!}) ⊕ {!!})
    run p = {!!}


module examples where
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

  p : Parses D w
  p =
    cons fzero (stepLiteral (
      cons (fsuc fzero) (stepLiteral (
        cons (fsuc fzero) (stepLiteral (
          cons fzero (stepLiteral (nil refl))))))))
