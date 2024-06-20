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

  data S where
    eff : Term F S
    lparenS+Frparen :
      Term
        ((literal lparen) ⊗ S ⊗ literal + ⊗ F ⊗ literal rparen)
        S
  data F where
    the-a : Term (literal a) F

  S-parser : Term (KL* ⊕Σ₀) (MaybeGrammar (LinΣ[ s ∈ String ] S))
  F-parser : Term (KL* ⊕Σ₀) (MaybeGrammar (LinΣ[ s ∈ String ] F))


  S-parser (GrammarDefs.nil x) =
    (MaybeGrammar-no-intro {g = ε-grammar} {h = S}) x
  -- lparen
  S-parser (GrammarDefs.cons (s , (fzero , lit) , kl)) =
    MaybeGrammar-bind
      {g =
        ((literal lparen) ⊗ S ⊗ literal + ⊗ F ⊗ literal rparen)}
      {h = S}
      (MaybeGrammar-yes-intro lparenS+Frparen)
      (trans {g = literal lparen ⊗ KL* ⊕Σ₀}
        {h =
         literal lparen ⊗
         (MaybeGrammar S ⊗ (literal + ⊗ (MaybeGrammar F ⊗ literal rparen)))}
        {k =
         MaybeGrammar
         (literal lparen ⊗ (S ⊗ (literal + ⊗ (F ⊗ literal rparen))))}
        (⊗-intro {g = literal lparen} {h = literal lparen} {k = KL* ⊕Σ₀}
          {l =
           MaybeGrammar S ⊗ (literal + ⊗ (MaybeGrammar F ⊗ literal rparen))}
          (id {g = literal lparen})
          {!!})
        {!!}
        (s , (lit , kl)))
  -- rparen
  S-parser (GrammarDefs.cons (s , (fsuc fzero , lit) , kl)) =
    MaybeGrammar-no-intro
      {g = literal rparen ⊗ KL* ⊕Σ₀} {h = S}
      (s , lit , kl)
  -- a
  S-parser (GrammarDefs.cons (s , (fsuc (fsuc fzero) , lit) , kl)) =
    MaybeGrammar-bind
      {g = F} {h = S}
      (MaybeGrammar-yes-intro eff)
      (F-parser (cons (s , (a , lit), kl)))
  -- +
  S-parser (GrammarDefs.cons (s , (fsuc (fsuc (fsuc fzero)) , lit) , kl)) =
    MaybeGrammar-no-intro
      {g = literal + ⊗ KL* ⊕Σ₀} {h = S}
      (s , lit , kl)

  F-parser (GrammarDefs.nil x) =
    (MaybeGrammar-no-intro {g = ε-grammar} {h = F}) x
  -- lparen
  F-parser (GrammarDefs.cons (s , (fzero , lit) , kl)) =
    MaybeGrammar-no-intro
      {g = literal lparen ⊗ KL* ⊕Σ₀} {h = F}
      (s , lit , kl)
  -- rparen
  F-parser (GrammarDefs.cons (s , (fsuc fzero , lit) , kl)) =
    MaybeGrammar-no-intro
      {g = literal rparen ⊗ KL* ⊕Σ₀} {h = F}
      (s , lit , kl)
  -- a
  F-parser (GrammarDefs.cons (s , (fsuc (fsuc fzero) , lit) , kl)) =
    MaybeGrammar-bind
      {g = literal a}
      {h = F}
     (MaybeGrammar-yes-intro the-a)
      (MaybeGrammar-bind
        {g = literal a ⊗ KL* ⊕Σ₀}
        {h = literal a }
        (-⊗-elim
          {g = literal a}
          {h = KL* ⊕Σ₀}
          {k = MaybeGrammar (literal a)}
          (foldKL*r
            {g = ⊕Σ₀}
            {h = literal a -⊗ MaybeGrammar (literal a)}
            (-⊗-intro
              {g = literal a}
              {h = ε-grammar}
              {k = MaybeGrammar (literal a)}
              (ε-extension-r
                {g = ε-grammar}
                {h = literal a}
                {k = MaybeGrammar (literal a)}
                (id {g = ε-grammar})
                (MaybeGrammar-return
                  {g = literal a} {h = literal a}
                  (id {g = literal a}))))
            (-⊗-intro
              {g = literal a }
              {h = ⊕Σ₀ ⊗ (literal a -⊗ MaybeGrammar (literal a))}
              {k = MaybeGrammar (literal a)}
              (MaybeGrammar-no-intro
                {g = literal a ⊗ ⊕Σ₀ ⊗ (literal a -⊗ MaybeGrammar (literal a))}
                {h = literal a})))
          (id {g = literal a}))
        (inl (s , (lit , kl)))
        )

  F-parser (GrammarDefs.cons (s , (fsuc (fsuc (fsuc fzero)) , lit) , kl)) =
    MaybeGrammar-no-intro
      {g = literal + ⊗ KL* ⊕Σ₀} {h = F}
      (s , lit , kl)

  -- testParser : Term (KL* ⊕Σ₀) (MaybeGrammar (S ⊗- ⊕Σ₀))
  -- -- empty
  -- testParser {w} x =
  --   foldKL*l
  --     {g = ⊕Σ₀}
  --     {h = MaybeGrammar (S ⊗- ⊕Σ₀)}
  --     (⊕-intro₂
  --       {g = ε-grammar}
  --       {h = (S ⊗- ⊕Σ₀)}
  --       {k = ⊤-grammar}
  --       (⊤-intro {g = ε-grammar}))
  --     (trans
  --       {g = MaybeGrammar (S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀}
  --       {h = MaybeGrammar ((S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀)}
  --       {k = MaybeGrammar (S ⊗- ⊕Σ₀)}
  -- -- : Term (MaybeGrammar (S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀)
  --   -- (MaybeGrammar ((S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀))
  --       {!!}
  -- -- : Term (MaybeGrammar ((S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀)) (MaybeGrammar (S ⊗- ⊕Σ₀))
  --       (MaybeGrammar-bind
  --         {g = (S ⊗- ⊕Σ₀) ⊗ ⊕Σ₀}
  --         {h = S ⊗- ⊕Σ₀}
  --         {!!}))
  --     (String→KL* w)

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
