{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp.Grammars where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Examples.BinOp.Alphabet

open import Grammar Alphabet hiding (_+)
open import Parser Alphabet
open import Term Alphabet
open import SemanticAction.Base Alphabet
open import Automata.Deterministic.Lookahead Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' : Level

module AST where
  data Exp : Type ℓ-zero where
    num : ℕ → Exp
    add : Exp → Exp → Exp

module Ambiguous where
  data Tag : Type ℓ-zero where
    num add parens : Tag

  ExpF : Functor Unit
  ExpF = ⊕e Tag (λ where
    num → k anyNum
    add → Var _ ⊗e k ＂ PLUS ＂ ⊗e Var _
    parens → k ＂ LP ＂ ⊗e Var _ ⊗e k ＂ RP ＂)

  -- TODO: come up with a better interface for writing semantic
  -- actions e.g., "pure" algebras
  semAct : SemanticAction (λ _ → ExpF) (λ _ → AST.Exp)
  semAct _ = ⊕ᴰ-elim λ where
    num → Pure-intro AST.num ∘g lowerG
    add → (⊕ᴰ-elim (λ er → Pure-intro (λ el → AST.add el er) ∘g ⊕ᴰ-distL .StrongEquivalence.fun)
      ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
      ∘g lowerG ,⊗ (⊕ᴰ-distR .StrongEquivalence.fun ∘g (id ,⊗ lowerG))
    parens → (Pure-intro (λ e → e) ∘g ⊕ᴰ-distR .StrongEquivalence.fun) ∘g id ,⊗ (⊕ᴰ-distL .StrongEquivalence.fun ∘g lowerG ,⊗ id)

module RightAssoc where
  data NT : Type ℓ-zero where
    Exp Atom : NT
  data Tag : (N : NT) → Type ℓ-zero where
    done add : Tag Exp
    num parens : Tag Atom

  BinOpF : NT → Functor NT
  BinOpF Exp = ⊕e (Tag Exp) λ where
    done → Var Atom
    add → Var Atom ⊗e k (literal PLUS) ⊗e Var Exp
  BinOpF Atom = ⊕e (Tag Atom) λ where
    num → k anyNum
    parens → k (literal LP) ⊗e Var Exp ⊗e k (literal RP)

  BinOp : NT → Grammar ℓ-zero
  BinOp = μ BinOpF

  -- TODO: RightAssoc is weakly equivalent to the ambiguous version (in fact a retract)
  module _ {X : Grammar ℓ} (ϕ : Algebra (λ _ → Ambiguous.ExpF) (λ _ → X)) where
    X' : NT → Grammar ℓ
    X' Exp = X
    X' Atom = X

    un-assoc-alg : Algebra BinOpF X'
    un-assoc-alg Exp = ⊕ᴰ-elim λ where
      done → lowerG
      add → ϕ _ ∘g σ Ambiguous.add
    un-assoc-alg Atom = ⊕ᴰ-elim λ where
      num → ϕ _ ∘g σ Ambiguous.num
      parens → ϕ _ ∘g σ Ambiguous.parens

module LeftFactorized where
  data NT : Type ℓ-zero where
    Exp dE/dA Atom : NT

  data Tag : NT → Type ℓ-zero where
    done add : Tag dE/dA
    num parens : Tag Atom

  BinOpF : NT → Functor NT
  BinOpF Exp = Var Atom ⊗e Var dE/dA
  BinOpF dE/dA = ⊕e (Tag dE/dA) λ where
    done → k ε
    add → k (literal PLUS) ⊗e Var Exp
  BinOpF Atom = ⊕e (Tag Atom) λ where
    num → k anyNum
    parens → k (literal LP) ⊗e Var Exp ⊗e k (literal RP)

  BinOp = μ BinOpF

  -- TODO: RightAssoc.BinOp Exp is strongly equivalent to BinOp Exp
  -- and analogous for RightAssoc.BinOp Atom
  module _ {X : RightAssoc.NT → Grammar ℓ} (ϕ : Algebra RightAssoc.BinOpF X) where
    X' : NT → Grammar ℓ
    X' Exp = X RightAssoc.Exp
    -- TODO: might need to use this instead
    -- X' dE/dA = ε ⊕ literal PLUS ⊗ X RightAssoc.Exp
    -- TODO: make this even more de-forested by eliminating this as well?
    X' dE/dA = X RightAssoc.Exp ⟜ X RightAssoc.Atom
    X' Atom = X RightAssoc.Atom

    un-factorize-alg : Algebra BinOpF X'
    un-factorize-alg Exp = ⟜-app ∘g lowerG ,⊗ lowerG
    un-factorize-alg dE/dA = ⊕ᴰ-elim λ where
      done → ⟜-intro (ϕ RightAssoc.Exp ∘g σ RightAssoc.done ∘g liftG ∘g ⊗-unit-r ∘g id ,⊗ lowerG)
      add → ⟜-intro (ϕ RightAssoc.Exp ∘g σ RightAssoc.add ∘g liftG ,⊗ id)
    un-factorize-alg Atom = ⊕ᴰ-elim λ where
      num    → ϕ RightAssoc.Atom ∘g σ RightAssoc.num
      parens → ϕ RightAssoc.Atom ∘g σ RightAssoc.parens

    -- un-factorize : ∀ nt → BinOp nt ⊢ X' nt
    -- un-factorize nt = {!!}
module LookaheadAutomaton where

  data State : Type ℓ-zero where
    Opening Closing Adding : ℕ → State
    fail : State

  aut : DeterministicAutomaton State
  aut .DeterministicAutomaton.init = Opening 0
  aut .DeterministicAutomaton.isAcc (Opening opens) = false
  aut .DeterministicAutomaton.isAcc (Closing opens) = false
  aut .DeterministicAutomaton.isAcc (Adding zero) = true
  aut .DeterministicAutomaton.isAcc (Adding (suc opens)) = false
  aut .DeterministicAutomaton.isAcc fail = false
  aut .DeterministicAutomaton.δ fail c g = fail
  aut .DeterministicAutomaton.δ (Opening opens) [ g = Opening (suc opens)
  aut .DeterministicAutomaton.δ (Opening opens) ] g = fail
  aut .DeterministicAutomaton.δ (Opening opens) + g = fail
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just ]) = Closing opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) nothing = Adding opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just +) = Adding opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just [) = fail
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just (num x₁)) = fail
  aut .DeterministicAutomaton.δ (Closing zero) ] g = fail
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just ]) = Closing opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] nothing = Adding opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just +) = Adding opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just [) = fail
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just (num x)) = fail
  aut .DeterministicAutomaton.δ (Closing opens) [ g = fail
  aut .DeterministicAutomaton.δ (Closing opens) + g = fail
  aut .DeterministicAutomaton.δ (Closing opens) (num x) g = fail
  aut .DeterministicAutomaton.δ (Adding opens) [ g = fail
  aut .DeterministicAutomaton.δ (Adding opens) ] g = fail
  aut .DeterministicAutomaton.δ (Adding opens) + g = Opening opens
  aut .DeterministicAutomaton.δ (Adding opens) (num x) g = fail

  module _ (X : LeftFactorized.NT → Grammar ℓ) (ϕ : Algebra LeftFactorized.BinOpF X) where
    -- Can we refunctionalize this?
    [Closing] : ℕ → Grammar ℓ
    [Closing] zero = ε*
    [Closing] (suc n) = literal RP ⊗ (literal PLUS ⊗ X LeftFactorized.Atom) * ⊗ [Closing] n

    X' : State → Grammar ℓ
    X' (Opening opens) = X LeftFactorized.Exp ⊗ [Closing] opens
    X' (Closing opens) = [Closing] opens
    X' (Adding opens)  = ((literal PLUS) ⊗ X LeftFactorized.Atom) ⊗ [Closing] opens
    X' fail = ⊥* -- TODO: make this better?

    [Opening] [Adding] : ℕ → Grammar _
    [Opening] n = X' (Opening n)
    [Adding] n = X' (Adding n)

    mkParseTreeAlg : Algebra (DeterministicAutomaton.TraceF aut true) X'
    mkParseTreeAlg (Opening x) = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim (λ ())
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim (λ where
        (lift ([ , g)) → {!!}
        (lift (] , g)) → {!!}
        (lift (+ , g)) → {!!}
        (lift (num n , nothing)) → {!!}
        (lift (num n , just [)) → {!!}
        (lift (num n , just ])) → {!!}
        (lift (num n , just +)) → {!!}
        (lift (num n , just (num m))) → {!!}))
    mkParseTreeAlg (Closing x) = {!!}
    mkParseTreeAlg (Adding x) = {!!}
    mkParseTreeAlg fail = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim (λ ())
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ _ →
        {!? ∘g !})

    X'' : Bool → State → Grammar ℓ
    X'' false = λ _ → ⊤*
    X'' true = X'

    parseTreeAlg : ∀ b → Algebra (DeterministicAutomaton.TraceF aut b) (X'' b)
    parseTreeAlg false = λ _ → ⊤*-intro
    parseTreeAlg true = mkParseTreeAlg

-- A completely deforested parse function
parse : string ⊢ Pure AST.Exp ⊕ ⊤
parse = ((⊕ᴰ-elim λ where
  false → inr ∘g ⊤-intro
  true → inl ∘g ⊗-unit-r ∘g id ,⊗ lowerG)
  ∘g π (LookaheadAutomaton.Opening 0))
  ∘g DeterministicAutomaton.parse-alg
       LookaheadAutomaton.aut
       (LookaheadAutomaton.parseTreeAlg _
         (LeftFactorized.un-factorize-alg (RightAssoc.un-assoc-alg Ambiguous.semAct)))
