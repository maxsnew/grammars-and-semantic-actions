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

    data DFATrace (q : Q .fst) (q-end : Q .fst) : String → Type ℓ where
      nil : ParseTransformer ε-grammar (DFATrace q q-end)
      cons : ∀ c →
        ParseTransformer
          (literal c ⊗ DFATrace (δ q c) q-end) (DFATrace q q-end)

    Parses : Grammar
    Parses =
      LinΣ[ q ∈ Σ[ q' ∈ Q .fst ] isAcc q' .fst .fst ] DFATrace init (q .fst)

    negate : DFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    δ negate = δ


--   open DFA

--   module _ (D : DFA) where
--     acceptingState : ∀ q w → DFATrace D q w → D .Q .fst
--     acceptingState q [] (nil x) = q
--     acceptingState q [] (cons c x) =
--       ⊥.rec (¬cons≡nil (sym the-string-path))
--       where
--       the-string-path =
--           (x .fst .snd ∙
--           cong (λ a → a ++ x .fst .fst .snd) (x .snd .fst))
--     acceptingState q (c ∷ w) (nil x) =
--       decRec
--         (λ acc → ⊥.rec
--           (¬cons≡nil (transport
--             (DecProp-grammar-yes-path (D .isAcc q) _ _ acc _) x) )
--           )
--         (λ ¬acc → ⊥.rec (lower (transport
--           (DecProp-grammar-no-path (D .isAcc q) _ _ ¬acc _) x)))
--         (D .isAcc q .snd)
--     acceptingState q (c ∷ w) (cons c' x) =
--       acceptingState (D .δ q c') w (
--         transport
--           (cong (λ z → DFATrace D (D .δ q c') z) x₁₁₂≡w)
--           (x .snd .snd))
--       where

--       the-string-path =
--           (x .fst .snd ∙
--           cong (λ a → a ++ x .fst .fst .snd) (x .snd .fst))

--       c≡c' : c ≡ c'
--       c≡c' = cons-inj₁ the-string-path

--       x₁₁₂≡w : x .fst .fst .snd ≡ w
--       x₁₁₂≡w = sym (cons-inj₂ the-string-path)

--     ¬D : DFA
--     ¬D = negate D

--     AcceptingAt : D .Q .fst → D .Q .fst → String → Type ℓ
--     AcceptingAt q-start q-end w =
--       Σ[ p ∈ DFATrace D q-start w ] acceptingState q-start w p ≡ q-end

--     run :
--       ParseTransformer
--         (KL* ⊕Σ₀)
--         ((LinΣ[ q ∈ (Σ[ q' ∈ D .Q .fst ] D .isAcc q' .fst .fst) ] {!!}) ⊕ {!!})
--     run p = {!!}


-- module examples where
--   open DFADefs ℓ-zero (Fin 2 , isFinSetFin)

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

--   p : Parses D w
--   p =
--     cons fzero (stepLiteral (
--       cons (fsuc fzero) (stepLiteral (
--         cons (fsuc fzero) (stepLiteral (
--           cons fzero (stepLiteral (nil refl))))))))
