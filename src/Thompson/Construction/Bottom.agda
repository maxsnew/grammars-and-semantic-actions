{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module Thompson.Construction.Bottom (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

import      Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (init ; rec ; map)
open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet.More
import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)
open import Cubical.Data.SumFin using (Fin ; fzero ; isSetFin ; discreteFin)
open import Cubical.Data.Unit
import Cubical.HITs.PropositionalTruncation as PT hiding (rec)

open import Grammar Alphabet
open import Automata.NFA.Base Alphabet
open import Term Alphabet

open StrongEquivalence

private
  variable ℓN ℓN' ℓP ℓ : Level

open NFA
open NFA.Accepting

-- Nullary Disjunction
module _ where
  ⊥NFA : NFA ℓ-zero
  ⊥NFA .Q = Unit , isFinSetUnit
  ⊥NFA .init = tt
  ⊥NFA .isAcc _ = false
  ⊥NFA .transition = Empty.⊥ , isFinSet⊥
  ⊥NFA .ε-transition = Empty.⊥ , isFinSet⊥

  ⊥NFA≅ : Parse ⊥NFA ≅ ⊥
  ⊥NFA≅ = mkStrEq
    (rec _ ⊥Alg _)
    ⊥-elim
    (⊥-η _ _)
    (equalizer-ind-unit (TraceTy ⊥NFA _)
      (⊕ᴰ≡ _ _ λ { (stop ()) }))
    where
      ⊥Alg : TraceAlg ⊥NFA λ _ → ⊥
      ⊥Alg tt = ⊕ᴰ-elim λ { (stop ()) }
