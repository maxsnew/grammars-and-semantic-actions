{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Automata.Implicit.AsDeterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Bool using (Bool ; false)

open import Automata.Implicit Alphabet
open import Automata.Deterministic Alphabet

private
  variable
    ℓ : Level

module _ (M : ImplicitDeterministicAutomaton ℓ) where
  open ImplicitDeterministicAutomaton M

  isAcc' : FreelyAddFail+Initial Q → Bool
  isAcc' fail    = false
  isAcc' initial = null
  isAcc' (↑q q)  = acc q

  δ' : FreelyAddFail+Initial Q → ⟨ Alphabet ⟩ → FreelyAddFail+Initial Q
  δ' fail    _ = fail
  δ' initial c = ↑f→q (δᵢ c)
  δ' (↑q q)  c = ↑f→q (δq q c)

  IDA→DA : DeterministicAutomaton (FreelyAddFail+Initial Q)
  IDA→DA .DeterministicAutomaton.init  = initial
  IDA→DA .DeterministicAutomaton.isAcc = isAcc'
  IDA→DA .DeterministicAutomaton.δ     = δ'
