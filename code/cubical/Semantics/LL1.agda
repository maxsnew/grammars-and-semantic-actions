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

  Str = KL* ⊕Σ₀

  S-parser : Term Str (MaybeGrammar (S ⊗ Str))
  F-parser : Term Str (MaybeGrammar (F ⊗ Str))

  Done : (G : Grammar) → Term (G ⊗ Str) (MaybeGrammar G)
  Done G (s , g , GrammarDefs.nil x) =
    -- TODO This is encodable in the language
    inl (transport (cong G (sym ((s .snd) ∙ (cong (s .fst .fst ++_) x) ∙ ++-unit-r (s .fst .fst)))) g)
    -- MaybeGrammar-yes-intro {g = G ⊗ Str} {h = G} {!!} (s , (g , (nil x)))
  Done G (s , g , GrammarDefs.cons x) = inr _


  S-parser (GrammarDefs.nil x) =
    MaybeGrammar-no-intro {g = Str} {h = S ⊗ Str} (nil x)
  -- lparen
  S-parser (GrammarDefs.cons (s , (fzero , lit) , kl)) =
    trans {g = literal lparen ⊗ Str}
     {h =
      MaybeGrammar (literal lparen) ⊗
      (MaybeGrammar S ⊗
       (MaybeGrammar (literal +) ⊗
        (MaybeGrammar F ⊗ (MaybeGrammar (literal rparen) ⊗ Str))))}
     {k = MaybeGrammar (S ⊗ Str)}
     help'
     help
     (s , (lit , kl))
    where
    help' :
      Term
      (literal lparen ⊗ Str)
      (
        MaybeGrammar (literal lparen) ⊗
        MaybeGrammar S ⊗
        MaybeGrammar (literal +) ⊗
        MaybeGrammar F ⊗
        MaybeGrammar (literal rparen) ⊗
        Str
      )
    help' = {!!}
    help :
      Term
      (
        MaybeGrammar (literal lparen) ⊗
        MaybeGrammar S ⊗
        MaybeGrammar (literal +) ⊗
        MaybeGrammar F ⊗
        MaybeGrammar (literal rparen) ⊗
        Str
      )
      (MaybeGrammar (S ⊗ Str))
    help = ?
    -- help (s , inl x , ss , inl x₁ , s+ , inl x₂ , sf , inl x₃ , sr , inl x₄ , str) =
    --   inl ({!!} , ((lparenS+Frparen
    --      (s , x , ss , (x₁ , (s+ , (x₂ , (sf , (x₃ , {!sr .snd!}))))))) , str))
    -- help (s , inl x , ss , inl x₁ , s+ , inl x₂ , sf , inl x₃ , sr , fsuc x₄ , str) = inr _
    -- help (s , inl x , ss , inl x₁ , s+ , inl x₂ , sf , fsuc x₃ , sr , mayr , str) = inr _
    -- help (s , inl x , ss , inl x₁ , s+ , fsuc x₂ , sf , mayf , sr , mayr , str) = inr _
    -- help (s , inl x , ss , fsuc x₁ , s+ , may+ , sf , mayf , sr , mayr , str) = inr _
    -- help (s , fsuc x , ss , mays , s+ , may+ , sf , mayf , sr , mayr , str) = inr _
  -- rparen
  S-parser (GrammarDefs.cons (s , (fsuc fzero , lit) , kl)) =
    MaybeGrammar-no-intro {g = Str} {h = S ⊗ Str} (cons (s , (rparen , lit) , kl))
  -- a
  S-parser (GrammarDefs.cons (s , (fsuc (fsuc fzero) , lit) , kl)) =
    MaybeGrammar-bind {g = F ⊗ Str} {h = S ⊗ Str}
      (trans {g = F ⊗ Str} {h = MaybeGrammar S ⊗ Str}
        {k = MaybeGrammar (S ⊗ Str)}
          (⊗-intro {g = F} {h = MaybeGrammar S} {k = Str} {l = Str}
            (MaybeGrammar-yes-intro {g = F} {h = S} eff)
            (id {g = Str}))
          help)
      (F-parser (cons (s , (a , lit), kl)))
      where
      -- TODO internalize
      help : Term (MaybeGrammar S ⊗ Str) (MaybeGrammar (S ⊗ Str))
      help (s , inl x , str) = inl (s , (x , str))
      help (s , inr x , str) = inr _
  -- +
  S-parser (GrammarDefs.cons (s , (fsuc (fsuc (fsuc fzero)) , lit) , kl)) =
    MaybeGrammar-no-intro {g =  Str} {h = S ⊗ Str} (cons (s , (+ , lit) , kl))

  F-parser (GrammarDefs.nil x) =
    MaybeGrammar-no-intro {g = Str} {h = F ⊗ Str} (nil x)
  -- lparen
  F-parser (GrammarDefs.cons (s , (fzero , lit) , kl)) =
    MaybeGrammar-no-intro {g = Str} {h = F ⊗ Str} (cons (s , (lparen , lit) , kl))
  -- rparen
  F-parser (GrammarDefs.cons (s , (fsuc fzero , lit) , kl)) =
    MaybeGrammar-no-intro {g = Str} {h = F ⊗ Str} (cons (s , (rparen , lit) , kl))
  -- a
  F-parser (GrammarDefs.cons (s , (fsuc (fsuc fzero) , lit) , kl)) =
    MaybeGrammar-yes-intro {g = literal a ⊗ Str} {h = F ⊗ Str}
      (⊗-intro {g = literal a} {h = F} {k = Str} {l = Str} the-a (id {g = Str}))
      (s , (lit , kl))
  -- +
  F-parser (GrammarDefs.cons (s , (fsuc (fsuc (fsuc fzero)) , lit) , kl)) =
    MaybeGrammar-no-intro {g = Str} {h = F ⊗ Str} (cons (s , (+ , lit) , kl))

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
