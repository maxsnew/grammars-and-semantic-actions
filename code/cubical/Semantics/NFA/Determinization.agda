{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
module Semantics.NFA.Determinization where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar
open import Semantics.DFA
open import Semantics.NFA.Base
open import Semantics.Helper
open import Semantics.Term
open import Semantics.String

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFADefs

module _ {ℓN} {Σ₀ : Type ℓ-zero}
  (N : NFA ℓN Σ₀) where
  open NFA N
  -- TODO make sure I don't include traces through states that i've already seen
--   data ε-reachable (q-end : Q .fst) : Q .fst → Type ℓ where
--     ε-reach-nil : ε-reachable q-end q-end
--     ε-reach-cons : ∀ (εtr : ε-transition .fst) →
--       ε-reachable q-end (ε-dst εtr) →
--       ε-reachable q-end (ε-src εtr)

--   ε-reachDecProp :
--     ∀ q-start q-end → DecProp ℓ
--   fst (fst (ε-reachDecProp q-start q-end)) = ∥ ε-reachable q-end q-start ∥₁
--   snd (fst (ε-reachDecProp q-start q-end)) = isPropPropTrunc
--   snd (ε-reachDecProp q-start q-end) =
--     decRec
--       (λ q-start≡q-end →
--         yes ∣ transport (cong (λ a → ε-reachable q-end a) (sym (q-start≡q-end))) ε-reach-nil ∣₁)
--       (λ ¬q-start≡q-end → {!!})
--       (decEqQ q-start q-end)

-- -- ε-reach : Q .fst → FinSetDecℙ Q .fst
-- -- ε-reach q-start q-end =
-- --   DecProp∃ {!!} {!!}
