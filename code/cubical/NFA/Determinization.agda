open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Determinization (Alphabet : hSet ℓ-zero) where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure
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

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import NFA.Base Alphabet
open import DFA Alphabet
open import Helper
open import Graph.Reachability

private
  variable
    ℓN : Level

open NFA

module _ (N : NFA {ℓN}) (isFinSetΣ₀ : isFinSet ⟨ Alphabet ⟩) where
  private
    module N = NFA N

  -- The NFA without labelled transitions, viewed as a directed graph
  open directedGraph
  ε-graph : directedGraph
  ε-graph .states = N.Q
  ε-graph .directed-edges = N.ε-transition
  ε-graph .src = N.ε-src
  ε-graph .dst = N.ε-dst

  -- The decidable finite set of states reachable from q-start
  ε-reach : ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
  ε-reach q-start q-end .fst .fst = _
  ε-reach q-start q-end .fst .snd = isPropPropTrunc
  ε-reach q-start q-end .snd = DecReachable ε-graph q-start q-end

  -- TODO: perhaps prove this is a closure,
  -- i.e. that the function is idempotent
  ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
  ε-closure X = FinSetDecℙ∃ N.Q N.Q X ε-reach

  δFunN : ⟨ N .Q ⟩ → ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ (N .Q) ⟩
  δFunN = N.hasTransition (isFinSet→Discrete isFinSetΣ₀)

  open DFA
  ℙN : DFA {ℓ-suc ℓN}
  ℙN .Q = FinSetDecℙ N.Q
  ℙN .init = ε-reach N.init
  ℙN .isAcc X =
    DecProp∃
      -- Quantifying over states in X : Σ[ q ∈ N .Q .fst ] X q .fst
      (Decℙ→FinSet (N .Q) X)
      -- Is any state in X accepting?
      (λ x → LiftDecProp (N .isAcc (x .fst)))
  ℙN .δ X c =
    ε-closure (FinSetDecℙ∃ N.Q N.Q (ε-closure X) (flip δFunN c))

  private
    module ℙN = DFA ℙN

  -- open N.Algebra
  -- open N.AlgebraHom
  -- NAlg : N.Algebra
  -- NAlg .the-ℓs _ = ℓ-suc ℓN
  -- NAlg .G q =
  --   LinΣ[ X ∈ (Σ[ Y ∈ ⟨ ℙN.Q ⟩ ] Y q .fst .fst) ] ℙN.ParseFrom (X .fst)
  -- NAlg .nil-case {q} qAcc _ pε = {!!}
  -- NAlg .cons-case = {!!}
  -- NAlg .ε-cons-case = {!!}

  -- open LogicalEquivalence
  -- N⊣⊢ℙN :
  --   LogicalEquivalence N.InitParse ℙN.InitParse
  -- N⊣⊢ℙN .fun = {!!}
  -- N⊣⊢ℙN .inv = {!!}
