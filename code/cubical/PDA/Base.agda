open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module PDA.Base
  (Alphabet (Γ₀ , isSetΓ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as DM
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin

open import Grammar Alphabet
open import Term Alphabet

private
  variable ℓP : Level

Stack = List Γ₀

-- Use push and withHead as an interface for manipulating the stack
-- of the PDA

-- Push the stack w onto st
-- w is reversed to give better readability
-- For example, we wish to say things like Z/AZ :
--   When Z is on the top of the stack, we pop Z and then replace it with AZ,
--   leaving Z to be the new top of the stack. And the top of the stack is
--   the left endpoint of the list, so AZ ought to be reversed before appending
push : Stack → Stack → Stack
push w st = (rev w) ++ st

withHead : Γ₀ → Stack → Stack
withHead γ s = γ ∷ s

record PDA : Type (ℓ-suc ℓP) where
  no-eta-equality
  field
    Q : FinSet ℓP
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → DecProp ℓP
    init-stack-sym : Γ₀
    transition : FinSet ℓP
    src : ⟨ transition ⟩ → ⟨ Q ⟩
    dst : ⟨ transition ⟩ → ⟨ Q ⟩
    label : ⟨ transition ⟩ → ⟨ Alphabet ⟩
    to-pop : ⟨ transition ⟩ → Γ₀
    to-push : ⟨ transition ⟩ → Stack
    ε-transition : FinSet ℓP
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-to-pop : ⟨ ε-transition ⟩ → Γ₀
    ε-to-push : ⟨ ε-transition ⟩ → Stack

  data Parse : (q : ⟨ Q ⟩) (s : Stack) → Grammar ℓP where
    nil : ∀ {q} → isAcc q .fst .fst →
      ε ⊢ Parse q []
    cons : ∀ t s →
      literal (label t) ⊗' Parse (dst t) (push (to-push t) s)
        ⊢
      Parse (src t) (withHead (to-pop t) s)
    ε-cons : ∀ t s →
      Parse (ε-dst t) (push (ε-to-push t) s)
        ⊢
      Parse (ε-src t) (withHead (ε-to-pop t) s)
