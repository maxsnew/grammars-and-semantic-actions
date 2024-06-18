{-# OPTIONS --lossy-unification #-}
module Semantics.LL1 where

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

module LL1Defs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open TermDefs ℓ (Σ₀ , isFinSetΣ₀)

module _ where
  open GrammarDefs ℓ-zero (Fin 4 , isFinSetFin)
  open StringDefs ℓ-zero (Fin 4 , isFinSetFin)
  open TermDefs ℓ-zero (Fin 4 , isFinSetFin)

  Σ₀ = Fin 4

  lparen : Fin 4
  lparen = fzero

  rparen : Fin 4
  rparen = fsuc fzero

  a : Fin 4
  a = fsuc (fsuc fzero)

  + : Fin 4
  + = fsuc (fsuc (fsuc fzero))

  data S : Grammar
  data F : Grammar

  -- S → ( S + F ) | F
  -- F → a

  -- TODO how do you specify the LL table in general?
  data S where
    eff : Term ((literal a -⊗ ⊤-grammar) & F) S
    lparenS+Frparen :
      Term
        ((literal lparen -⊗ ⊤-grammar) & ((literal lparen) ⊗ S ⊗ literal + ⊗ F ⊗ literal rparen))
        S
  data F where
    the-a : Term ((literal a -⊗ ⊤-grammar) & literal a) F

  testParser : Term (KL* ⊕Σ₀) (S ⊕ ⊤-grammar)
  -- empty
  testParser x =
    foldKL*l
      {g = ⊕Σ₀}
      {h = S ⊕ ⊤-grammar}
      (⊕-intro₂
        {g = ε-grammar}
        {h = S}
        {k = ⊤-grammar}
        (⊤-intro {g = ε-grammar}))
      {!!}
      {!!}

  -- testParser (nil x) = inr _
  -- -- lparen
  -- testParser (cons (spl , (fzero , litx) , w)) =
  --   let the-S = {!!} in
  --   let the-F = {!!} in
  --   {!S.lparenS+Frparen ?!}
  -- -- rparen
  -- testParser (cons (spl , (fsuc fzero , litx) , w)) = {!!}
  -- -- a
  -- testParser (cons (spl , (fsuc (fsuc fzero) , litx) , w)) = {!!}
  -- -- +
  -- testParser (cons (spl , (fsuc (fsuc (fsuc fzero)) , litx) , w)) = {!!}
