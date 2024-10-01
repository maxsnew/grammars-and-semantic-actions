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
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import NFA.Base Alphabet
open import DFA Alphabet
open import Helper
open import Graph.Reachability

private
  variable
    ℓN ℓ : Level

open NFA

module _ (N : NFA {ℓN}) (isFinSetΣ₀ : isFinSet ⟨ Alphabet ⟩) where
  private
    module N = NFA N

  is-ε-closed : ⟨ FinSetDecℙ N.Q ⟩ → Type ℓN
  is-ε-closed X = (t : ⟨ N.ε-transition ⟩) (x : ⟨ N.Q ⟩) (x∈X : X x .fst .fst) →
    N.ε-src t ≡ x → X (N.ε-dst t) .fst .fst

  ε-closed : Type (ℓ-suc ℓN)
  ε-closed = Σ ⟨ FinSetDecℙ N.Q ⟩ is-ε-closed

  _∈-ε-closed_ : ⟨ N.Q ⟩ → ε-closed → Type ℓN
  q ∈-ε-closed qs = qs .fst q .fst .fst

  -- The NFA without labelled transitions, viewed as a directed graph
  open directedGraph
  ε-graph : directedGraph
  ε-graph .states = N.Q
  ε-graph .directed-edges = N.ε-transition
  ε-graph .src = N.ε-src
  ε-graph .dst = N.ε-dst
  private module ε-graph = directedGraph ε-graph

  opaque
    -- The decidable finite set of states reachable from q-start
    ε-reach : ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    ε-reach q-start q-end .fst = _ , isPropPropTrunc
    ε-reach q-start q-end .snd = DecReachable ε-graph q-start q-end

    ε-reach-is-ε-closed : ∀ q-start → is-ε-closed (ε-reach q-start)
    ε-reach-is-ε-closed q-start t x x-is-reachable src≡x = do
      (n , gw , q-start≡start-gw , x≡end-gw) ← x-is-reachable
      return
        (suc n ,
        ε-graph.snoc t gw (src≡x ∙ x≡end-gw) ,
        q-start≡start-gw ∙ ε-graph.snoc-pres-start t gw (src≡x ∙ x≡end-gw) ,
        ε-graph.snoc-end t gw (src≡x ∙ x≡end-gw))
      where open PTMonad

    ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ε-closed
    ε-closure X .fst = FinSetDecℙ∃ N.Q N.Q X ε-reach
    ε-closure X .snd t x x∈X src≡x = do
      (a , a∈X , reach) ← x∈X
      return (a , a∈X , ε-reach-is-ε-closed a t x reach src≡x)
      where open PTMonad

    ε-closure-lift-∈ :
      {A : Decℙ ⟨ N.Q ⟩} {a : ⟨ N.Q ⟩} →
      _∈-FinSetDecℙ_ {A = N.Q} a A → a ∈-ε-closed (ε-closure A)
    ε-closure-lift-∈ a∈A = ∣ _ , a∈A , (Reachable-is-reflexive ε-graph _) ∣₁

  opaque
    lit-reach : ⟨ Alphabet ⟩ → ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-reach c q-start = N.hasTransition (isFinSet→Discrete isFinSetΣ₀) q-start c

    lit-closure : ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-closure c X = FinSetDecℙ∃ N.Q N.Q X (lit-reach c)

  data DetTrace : ε-closed → Grammar (ℓ-suc ℓN) where
    det-nil : ε ⊢ DetTrace (ε-closure N.isAcc)
    det-cons : ∀ {c qs} → literal c ⊗ DetTrace qs ⊢ DetTrace (ε-closure (lit-closure c (qs .fst)))

  det-cons-LinΣ : char ⊗ LinearΣ DetTrace ⊢ LinearΣ DetTrace
  det-cons-LinΣ =
    ⊸-app
    ∘g ⊗-intro id
      (LinΣ-elim (λ qs →
        ⊸-intro {k = LinearΣ DetTrace}
          (⟜-app
          ∘g ⊗-intro
            (LinΣ-elim (λ c → ⟜-intro (LinΣ-intro {h = DetTrace} (ε-closure (lit-closure c (qs .fst))) ∘g det-cons)))
            id)))

  parse : string ⊢ LinΣ[ qs ∈ ε-closed ] DetTrace qs
  parse = foldKL*r char (record
    { the-ℓ = _
    ; G = _
    ; nil-case = LinΣ-intro _ ∘g det-nil
    ; cons-case = det-cons-LinΣ
    })

  extract : ∀ q qs → q ∈-ε-closed qs → DetTrace qs ⊢ N.Parse q
  extract q qs q∈qs = {!!}

  witness : ∀ q →
    N.Parse q ⊢ LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
  witness q = N.recTrace (record
    { the-ℓs = _
    ; G = λ q → LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
    ; nil-case = λ is-acc →
      LinΣ-intro (ε-closure N.isAcc)
      ∘g LinΣ-intro (ε-closure-lift-∈ is-acc)
      ∘g det-nil
    ; cons-case = λ tr → ⊸-app ∘g ⊗-intro id (LinΣ-elim (λ qs → {!!}))
    ; ε-cons-case = {!!}
    })

  -- -- TODO: perhaps prove this is a closure,
  -- -- i.e. that the function is idempotent
  -- ℙ-ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
  -- ℙ-ε-closure X = FinSetDecℙ∃ N.Q N.Q X ε-reach

  -- δFunN : ⟨ N.Q ⟩ → ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩
  -- δFunN = N.hasTransition (isFinSet→Discrete isFinSetΣ₀)

  -- data DetTrace : {!!} → Grammar (ℓ-suc ℓN) where
  --   nil : ε ⊢ DetTrace {!!}

  -- open DFA
  -- ℙN : DFA {ℓ-suc ℓN}
  -- ℙN .Q = FinSetDecℙ N.Q
  -- ℙN .init = ε-reach N.init
  -- ℙN .isAcc X =
  --   DecProp∃
  --     -- Quantifying over states in X : Σ[ q ∈ N .Q .fst ] X q .fst
  --     (Decℙ→FinSet (N .Q) X)
  --     -- Is any state in X accepting?
  --     (λ x → LiftDecProp (N .isAcc (x .fst)))
  -- ℙN .δ X c =
  --   ε-closure (FinSetDecℙ∃ N.Q N.Q (ε-closure X) (flip δFunN c))

  -- private
  --   module ℙN = DFA ℙN

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

