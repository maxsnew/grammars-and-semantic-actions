open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Determinization (Alphabet : hSet ℓ-zero) where

-- open import Cubical.Reflection.RecordEquiv
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Powerset
-- open import Cubical.Foundations.Structure
-- open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
-- open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.Constructors
-- open import Cubical.Data.FinSet.DecidablePredicate
-- open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
-- open import Cubical.Data.W.Indexed
-- open import Cubical.Data.Maybe
-- open import Cubical.Data.FinSet.Constructors
-- open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
import Cubical.Data.Equality as Eq
-- open import Cubical.Data.Nat.Order.Recursive as Ord
-- open import Cubical.Data.SumFin
-- open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
-- open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet
open import NFA.Base Alphabet
open import DFA Alphabet
open import Helper
open import Graph.Reachability

private
  variable
    ℓN ℓ : Level

open NFA
open StrongEquivalence

module _ (N : NFA) (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩ ) where
  private
    module N = NFA N

  is-ε-closed : ⟨ FinSetDecℙ N.Q ⟩ → Type ℓ-zero
  is-ε-closed X = (t : ⟨ N.ε-transition ⟩) (x : ⟨ N.Q ⟩) (x∈X : X x .fst .fst) →
    N.ε-src t ≡ x → X (N.ε-dst t) .fst .fst

  ε-closed : Type (ℓ-suc ℓ-zero)
  ε-closed = Σ ⟨ FinSetDecℙ N.Q ⟩ is-ε-closed

  _∈-ε-closed_ : ⟨ N.Q ⟩ → ε-closed → Type ℓ-zero
  q ∈-ε-closed qs = qs .fst q .fst .fst

  open directedGraph
  -- The NFA without labelled transitions,
  -- viewed as a directed graph
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

    ε-closure-transition :
      (t : ⟨ N.ε-transition ⟩) →
      (X : ε-closed) →
      N.ε-src t ∈-ε-closed X →
      N.ε-dst t ∈-ε-closed X
    ε-closure-transition t X src∈X = X .snd t (N.ε-src t) src∈X refl


  opaque
    unfolding ε-closure
    lit-reach : ⟨ Alphabet ⟩ → ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-reach c q-start =
      N.hasTransition (isFinSet→Discrete isFinSetAlphabet) q-start c

    lit-closure : ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-closure c X = FinSetDecℙ∃ N.Q N.Q X (lit-reach c)

    lit-closure-transition :
      (t : ⟨ N.transition ⟩) →
      (X : ε-closed) →
      N.src t ∈-ε-closed X →
      N.dst t ∈-ε-closed ε-closure (lit-closure (N.label t) (X .fst))
    lit-closure-transition t X src∈X =
      ∣ (N.dst t) ,
        (∣ (N.src t) , (src∈X , ∣ t , refl , (refl , refl) ∣₁) ∣₁ ,
          ∣ 0 , (trivialWalk ε-graph (N.dst t) , (refl , refl)) ∣₁) ∣₁

  data DetTag : Type₁ where
    stop step : DetTag

  module _ (X-end : ε-closed) where
    DetTraceTy : (X : ε-closed) → Functor ε-closed
    DetTraceTy X = ⊕e DetTag λ {
        stop → ⊕e (X Eq.≡ X-end ) λ { Eq.refl → k (LiftGrammar ε) }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) λ {
        (lift c) →
          ⊗e (k (LiftGrammar (literal c)))
             (Var (ε-closure (lit-closure c (X .fst))))
      } }

  DetTrace : (X-end X : ε-closed) → Grammar (ℓ-suc ℓ-zero)
  DetTrace X-end X = μ (DetTraceTy X-end) X

  NFATraceTyLift :
    Bool →
    Lift {ℓ-zero}{ℓ-suc ℓ-zero}(⟨ N.Q ⟩) →
    Functor {ℓ = ℓ-suc ℓ-zero} (Lift ⟨ N.Q ⟩)
  NFATraceTyLift b (lift q) = ⊕e (Lift N.Tag)
    (λ {(lift stop) →
      ⊕e (Lift (b Eq.≡ N.isAcc q))
        λ {(lift Eq.refl) → k (LiftGrammar ε)}
      ; (lift step) → ⊕e (Lift (Eq.fiber N.src q))
        λ { (lift (t , Eq.refl)) →
          ⊗e (k (LiftGrammar (literal (N.label t)))) (Var (lift (N.dst t))) }
      ; (lift stepε) → ⊕e (Lift (Eq.fiber N.ε-src q))
        (λ {(lift (t , Eq.refl)) → Var (lift (N.ε-dst t))}) })

  NFA→DFA-alg : ∀ b →
    Algebra (NFATraceTyLift b)
      (λ q →
        &[ X ∈ ε-closed ]
        &[ a ∈ (lower q) ∈-ε-closed X ]
        ⊕[ X-end ∈ ε-closed ] DetTrace X-end X)
  NFA→DFA-alg b (lift q) = ⊕ᴰ-elim (λ {
      (lift stop) →
        ⊕ᴰ-elim λ { (lift Eq.refl) →
          &ᴰ-in (λ X → &ᴰ-in (λ q∈X →
            ⊕ᴰ-in X ∘g
            roll ∘g
            ⊕ᴰ-in stop ∘g
            ⊕ᴰ-in Eq.refl
            )) }
    ; (lift step) → ⊕ᴰ-elim (λ { (lift (t , Eq.refl)) →
        &ᴰ-in (λ X → &ᴰ-in λ src∈X →
          ⊕ᴰ-elim (λ X-end →
            ⊕ᴰ-in X-end ∘g
            roll ∘g
            ⊕ᴰ-in step ∘g
            ⊕ᴰ-in (lift (N.label t))
            ) ∘g
          ⊕ᴰ-distR .fun ∘g
          id ,⊗ &ᴰ-π (lit-closure-transition t X src∈X) ∘g
          id ,⊗ &ᴰ-π (ε-closure (lit-closure (N.label t) (X .fst)))
          )
      })
    ; (lift stepε) → ⊕ᴰ-elim (λ { (lift (t , Eq.refl)) →
        &ᴰ-in (λ X → &ᴰ-in (λ src∈X →
          &ᴰ-π (ε-closure-transition t X src∈X) ∘g
          &ᴰ-π X
          ))
        }) })

  -- ⊕e TraceTag λ {
  --   stop → ⊕e (b Eq.≡ isAcc q) λ { Eq.refl → k ε }
  --   ; step → ⊕e ⟨ Alphabet ⟩ λ c → ⊗e (k (literal c)) (Var (δ q c)) }

  -- Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓ-zero
  -- Trace b = μ (TraceTy b)

  -- open DFA
--   ℙN : DFA
--   ℙN .Q = (∀ (q : ⟨ N.Q ⟩) → Bool) , isFinSet→ N.Q (Bool , isFinSetBool)
--   ℙN .init = λ q →
--     decRec
--       (λ _ → true)
--       (λ _ → false)
--       (ε-closure (SingletonDecℙ {A = N.Q} (N .init)) .fst q .snd)
--   ℙN .isAcc f =
--     decRec
--       (λ _ → true)
--       (λ _ → false)
--       (DecProp∃
--         N.Q
--         (λ x →
--           DecProp×
--             (DecProp≡ (isFinSet→Discrete isFinSetBool)
--             (f x)
--             true)
--             (Bool≃DecProp .fst (N.isAcc x)))
--         .snd)
--   ℙN .δ f c = λ q →
--     decRec
--       (λ _ → true)
--       (λ _ → false)
--       (lit-closure c (λ x → Bool≃DecProp .fst (f x)) q .snd)

--   private
--     module ℙN = DFA ℙN

--   N⊢ℙNAlg : ∀ b →
--     Algebra
--       (N.TraceTy b)
--       (λ q → &[ Q ∈ ⟨ ℙN.Q ⟩ ] ⊕[ a ∈ true Eq.≡ Q q ] ℙN.Trace b Q )
--   N⊢ℙNAlg b q =
--     ⊕ᴰ-elim (λ {
--       stop → &ᴰ-in (λ Q → ⊕ᴰ-elim (λ { Eq.refl →
--       ⊕ᴰ-in {!!} ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in {!Eq.refl!} }))
--     ; step → {!!}
--     ; stepε → {!!} })

-- --   data DetTrace : ε-closed → Grammar (ℓ-suc ℓN) where
-- --     det-nil : ε ⊢ DetTrace (ε-closure N.isAcc)
-- --     det-cons : ∀ {c qs} → literal c ⊗ DetTrace qs ⊢ DetTrace (ε-closure (lit-closure c (qs .fst)))

-- --   det-cons-LinΣ : char ⊗ LinearΣ DetTrace ⊢ LinearΣ DetTrace
-- --   det-cons-LinΣ =
-- --     ⊸-app
-- --     ∘g ⊗-intro id
-- --       (LinΣ-elim (λ qs →
-- --         ⊸-intro {k = LinearΣ DetTrace}
-- --           (⟜-app
-- --           ∘g ⊗-intro
-- --             (LinΣ-elim (λ c → ⟜-intro (LinΣ-intro {h = DetTrace} (ε-closure (lit-closure c (qs .fst))) ∘g det-cons)))
-- --             id)))

-- --   parse : string ⊢ LinΣ[ qs ∈ ε-closed ] DetTrace qs
-- --   parse = foldKL*r char (record
-- --     { the-ℓ = _
-- --     ; G = _
-- --     ; nil-case = LinΣ-intro _ ∘g det-nil
-- --     ; cons-case = det-cons-LinΣ
-- --     })

-- --   extract : ∀ q qs → q ∈-ε-closed qs → DetTrace qs ⊢ N.Parse q
-- --   extract q qs q∈qs = {!!}

-- --   witness : ∀ q →
-- --     N.Parse q ⊢ LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
-- --   witness q = N.recTrace (record
-- --     { the-ℓs = _
-- --     ; G = λ q → LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
-- --     ; nil-case = λ is-acc →
-- --       LinΣ-intro (ε-closure N.isAcc)
-- --       ∘g LinΣ-intro (ε-closure-lift-∈ is-acc)
-- --       ∘g det-nil
-- --     ; cons-case = λ tr → ⊸-app ∘g ⊗-intro id (LinΣ-elim (λ qs → {!!}))
-- --     ; ε-cons-case = {!!}
-- --     })

-- --   -- -- TODO: perhaps prove this is a closure,
-- --   -- -- i.e. that the function is idempotent
-- --   -- ℙ-ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
-- --   -- ℙ-ε-closure X = FinSetDecℙ∃ N.Q N.Q X ε-reach

-- --   -- δFunN : ⟨ N.Q ⟩ → ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩
-- --   -- δFunN = N.hasTransition (isFinSet→Discrete isFinSetΣ₀)

-- --   -- data DetTrace : {!!} → Grammar (ℓ-suc ℓN) where
-- --   --   nil : ε ⊢ DetTrace {!!}

-- --   -- open DFA
-- --   -- ℙN : DFA {ℓ-suc ℓN}
-- --   -- ℙN .Q = FinSetDecℙ N.Q
-- --   -- ℙN .init = ε-reach N.init
-- --   -- ℙN .isAcc X =
-- --   --   DecProp∃
-- --   --     -- Quantifying over states in X : Σ[ q ∈ N .Q .fst ] X q .fst
-- --   --     (Decℙ→FinSet (N .Q) X)
-- --   --     -- Is any state in X accepting?
-- --   --     (λ x → LiftDecProp (N .isAcc (x .fst)))
-- --   -- ℙN .δ X c =
-- --   --   ε-closure (FinSetDecℙ∃ N.Q N.Q (ε-closure X) (flip δFunN c))

-- --   -- private
-- --   --   module ℙN = DFA ℙN

-- --   -- open N.Algebra
-- --   -- open N.AlgebraHom
-- --   -- NAlg : N.Algebra
-- --   -- NAlg .the-ℓs _ = ℓ-suc ℓN
-- --   -- NAlg .G q =
-- --   --   LinΣ[ X ∈ (Σ[ Y ∈ ⟨ ℙN.Q ⟩ ] Y q .fst .fst) ] ℙN.ParseFrom (X .fst)
-- --   -- NAlg .nil-case {q} qAcc _ pε = {!!}
-- --   -- NAlg .cons-case = {!!}
-- --   -- NAlg .ε-cons-case = {!!}

-- --   -- open LogicalEquivalence
-- --   -- N⊣⊢ℙN :
-- --   --   LogicalEquivalence N.InitParse ℙN.InitParse
-- --   -- N⊣⊢ℙN .fun = {!!}
-- --   -- N⊣⊢ℙN .inv = {!!}
