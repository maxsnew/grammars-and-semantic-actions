open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Determinization (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.Empty as Empty hiding (rec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Nat
import Cubical.Data.Equality as Eq


open import Cubical.HITs.PropositionalTruncation as PT hiding (rec)
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad

open import Grammar Alphabet
open import Grammar.Lift Alphabet
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
  is-ε-closed X =
    (t : ⟨ N.ε-transition ⟩) (x : ⟨ N.Q ⟩)
    (src∈X : X (N.ε-src t) .fst .fst) →
    X (N.ε-dst t) .fst .fst

  isProp-is-ε-closed : ∀ X → isProp (is-ε-closed X)
  isProp-is-ε-closed X a b =
    funExt λ t → funExt λ x → funExt (λ src∈X →
      X (N.ε-dst t) .fst .snd (a t x src∈X) (b t x src∈X))

  Dec-is-ε-closed : ∀ X → Dec (is-ε-closed X)
  Dec-is-ε-closed X =
    decRec
      (λ ∣t,src∈X,¬dst∈X∣ →
        PT.rec
          (isPropDec (isProp-is-ε-closed X))
          (λ (t , src∈X , ¬dst∈X) →
            no (λ closed → ¬dst∈X (closed t (N.ε-src t) src∈X)))
          ∣t,src∈X,¬dst∈X∣)
      (λ ¬|t,src∈X,¬dst∈X| →
            yes (λ t x src∈X →
              decRec
                (λ dst∈X → dst∈X)
                (λ ¬dst∈X →
                  Empty.rec
                    (¬|t,src∈X,¬dst∈X| ∣ t , src∈X , ¬dst∈X ∣₁))
                (X (N.ε-dst t) .snd)))
      (DecProp∃
        N.ε-transition
        (λ t →
          DecProp×
            (X (N.ε-src t))
            (negateDecProp (X (N.ε-dst t))))
        .snd)

  isFinSet-is-ε-closed : ∀ X → isFinSet (is-ε-closed X)
  isFinSet-is-ε-closed X =
    isDecProp→isFinSet
      (isProp-is-ε-closed X)
      (Dec-is-ε-closed X)

  ε-closed : Type (ℓ-suc ℓ-zero)
  ε-closed = Σ ⟨ FinSetDecℙ N.Q ⟩ is-ε-closed

  isFinSet-ε-closed : isFinSet ε-closed
  isFinSet-ε-closed =
    isFinSetΣ (FinSetDecℙ N.Q) λ X → _ , (isFinSet-is-ε-closed X)

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
    ε-reach-is-ε-closed q-start t x x-is-reachable = do
      (n , gw , q-start≡start-gw , x≡end-gw) ← x-is-reachable
      return
        (suc n ,
        ε-graph.snoc t gw x≡end-gw ,
        q-start≡start-gw ∙ ε-graph.snoc-pres-start t gw x≡end-gw ,
        ε-graph.snoc-end t gw x≡end-gw)
      where open PTMonad

    ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ε-closed
    ε-closure X .fst = FinSetDecℙ∃ N.Q N.Q X ε-reach
    ε-closure X .snd t x x∈X = do
      (a , a∈X , reach) ← x∈X
      return (a , a∈X , ε-reach-is-ε-closed a t x reach)
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
    ε-closure-transition t X src∈X = X .snd t (N.ε-src t) src∈X

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
        (∣ (N.src t) , (src∈X , ∣ t , (refl , refl , refl) ∣₁) ∣₁ ,
          ∣ 0 , ((trivialWalk ε-graph (N.dst t)) , (refl , refl)) ∣₁) ∣₁

  open DFA
  ℙN : DFA {ℓD = ℓ-suc ℓ-zero}
  ℙN .Q = ε-closed , isFinSet-ε-closed
  ℙN .init = ε-closure (SingletonDecℙ {A = N.Q} N.init)
  ℙN .isAcc X =
    Bool≃DecProp .snd .equiv-proof
      (DecProp∃
        N.Q
        (λ q → DecProp× (X .fst q) (Bool≃DecProp .fst (N.isAcc q))))
      .fst .fst
    -- decRec
    --   (λ _ → true)
    --   (λ _ → false)
    --   (DecProp∃
    --     N.Q
    --     (λ q → DecProp× (X .fst q) (Bool≃DecProp .fst (N.isAcc q)))
    --     .snd)
  ℙN .δ X c = ε-closure (lit-closure c (X .fst))

  private
    module ℙN = DFA ℙN

  NFA→DFA-alg : ∀ b →
    Algebra (N.TraceTy b)
      (λ q →
        &[ X ∈ ε-closed ]
        &[ q∈X ∈ q ∈-ε-closed X ] ℙN.Trace b X
      )
  NFA→DFA-alg b q =
    ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim (λ {
          (lift Eq.refl) → &ᴰ-in λ X →
            &ᴰ-in (λ q∈X →
              roll ∘g
              ⊕ᴰ-in ℙN.stop ∘g
              -- q is accepting and q is in X, so we need
              -- to combine these to show that X is accepting
              ⊕ᴰ-in (lift {!!}) ∘g
              liftG ∘g
              lowerG ∘g
              lowerG
            ) })
      ; step → ⊕ᴰ-elim (λ { (t , Eq.refl) →
        &ᴰ-in (λ X → &ᴰ-in λ src∈X →
          roll ∘g
          ⊕ᴰ-in ℙN.step ∘g
          ⊕ᴰ-in (lift (N.label t)) ∘g
          liftG ,⊗ id ∘g
          liftG ,⊗ liftG ∘g
          id ,⊗ &ᴰ-π (lit-closure-transition t X src∈X) ∘g
          id ,⊗ &ᴰ-π (ε-closure (lit-closure (N.label t) (X .fst))) ∘g
          lowerG ,⊗ id ∘g
          lowerG ,⊗ lowerG
          )
          })
      ; stepε →
        ⊕ᴰ-elim λ { (t , Eq.refl) →
          &ᴰ-in (λ X → &ᴰ-in (λ src∈X →
            &ᴰ-π (ε-closure-transition t X src∈X) ∘g
            &ᴰ-π X)) ∘g
          lowerG } })

  NFA→DFA : ∀ b q →
    N.Trace b q ⊢
      &[ X ∈ ε-closed ]
      &[ q∈X ∈ q ∈-ε-closed X ] ℙN.Trace b X
  NFA→DFA b q = rec (N.TraceTy b) (NFA→DFA-alg b) q



  DFA→NFA-alg : ∀ b →
    Algebra (ℙN.TraceTy b)
      (λ X → ⊕[ q ∈ ⟨ N.Q ⟩ ] ⊕[ q∈X ∈ q ∈-ε-closed X ] N.Trace b q)
  DFA→NFA-alg b X =
    ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) →
        ⊕ᴰ-in {!!} ∘g
        ⊕ᴰ-in {!!} ∘g
        roll ∘g
        ⊕ᴰ-in N.stop ∘g
        ⊕ᴰ-in (lift {!!}) ∘g
        lowerG ∘g
        lowerG
      })
    ; step → ⊕ᴰ-elim (λ { (lift c) →
      ⊕ᴰ-elim (λ q →
        ⊕ᴰ-elim (λ q∈X →
          ⊕ᴰ-in ? ∘g
          ⊕ᴰ-in {!!} ∘g
          roll ∘g
          ⊕ᴰ-in N.step ∘g
          ⊕ᴰ-in ({!!} , {!!})
          ) ∘g
        ⊕ᴰ-distR .fun
      ) ∘g
      ⊕ᴰ-distR .fun ∘g
      lowerG ,⊗ id ∘g
      lowerG ,⊗ lowerG
    }) })

-- --   -- ⊕e TraceTag λ {
-- --   --   stop → ⊕e (b Eq.≡ isAcc q) λ { Eq.refl → k ε }
-- --   --   ; step → ⊕e ⟨ Alphabet ⟩ λ c → ⊗e (k (literal c)) (Var (δ q c)) }

-- --   -- Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓ-zero
-- --   -- Trace b = μ (TraceTy b)

-- --   -- open DFA
-- -- --   ℙN : DFA
-- -- --   ℙN .Q = (∀ (q : ⟨ N.Q ⟩) → Bool) , isFinSet→ N.Q (Bool , isFinSetBool)
-- -- --   ℙN .init = λ q →
-- -- --     decRec
-- -- --       (λ _ → true)
-- -- --       (λ _ → false)
-- -- --       (ε-closure (SingletonDecℙ {A = N.Q} (N .init)) .fst q .snd)
-- -- --   ℙN .isAcc f =
-- -- --     decRec
-- -- --       (λ _ → true)
-- -- --       (λ _ → false)
-- -- --       (DecProp∃
-- -- --         N.Q
-- -- --         (λ x →
-- -- --           DecProp×
-- -- --             (DecProp≡ (isFinSet→Discrete isFinSetBool)
-- -- --             (f x)
-- -- --             true)
-- -- --             (Bool≃DecProp .fst (N.isAcc x)))
-- -- --         .snd)
-- -- --   ℙN .δ f c = λ q →
-- -- --     decRec
-- -- --       (λ _ → true)
-- -- --       (λ _ → false)
-- -- --       (lit-closure c (λ x → Bool≃DecProp .fst (f x)) q .snd)

-- -- --   private
-- -- --     module ℙN = DFA ℙN

-- -- --   N⊢ℙNAlg : ∀ b →
-- -- --     Algebra
-- -- --       (N.TraceTy b)
-- -- --       (λ q → &[ Q ∈ ⟨ ℙN.Q ⟩ ] ⊕[ a ∈ true Eq.≡ Q q ] ℙN.Trace b Q )
-- -- --   N⊢ℙNAlg b q =
-- -- --     ⊕ᴰ-elim (λ {
-- -- --       stop → &ᴰ-in (λ Q → ⊕ᴰ-elim (λ { Eq.refl →
-- -- --       ⊕ᴰ-in {!!} ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in {!Eq.refl!} }))
-- -- --     ; step → {!!}
-- -- --     ; stepε → {!!} })

-- -- -- --   data DetTrace : ε-closed → Grammar (ℓ-suc ℓN) where
-- -- -- --     det-nil : ε ⊢ DetTrace (ε-closure N.isAcc)
-- -- -- --     det-cons : ∀ {c qs} → literal c ⊗ DetTrace qs ⊢ DetTrace (ε-closure (lit-closure c (qs .fst)))

-- -- -- --   det-cons-LinΣ : char ⊗ LinearΣ DetTrace ⊢ LinearΣ DetTrace
-- -- -- --   det-cons-LinΣ =
-- -- -- --     ⊸-app
-- -- -- --     ∘g ⊗-intro id
-- -- -- --       (LinΣ-elim (λ qs →
-- -- -- --         ⊸-intro {k = LinearΣ DetTrace}
-- -- -- --           (⟜-app
-- -- -- --           ∘g ⊗-intro
-- -- -- --             (LinΣ-elim (λ c → ⟜-intro (LinΣ-intro {h = DetTrace} (ε-closure (lit-closure c (qs .fst))) ∘g det-cons)))
-- -- -- --             id)))

-- -- -- --   parse : string ⊢ LinΣ[ qs ∈ ε-closed ] DetTrace qs
-- -- -- --   parse = foldKL*r char (record
-- -- -- --     { the-ℓ = _
-- -- -- --     ; G = _
-- -- -- --     ; nil-case = LinΣ-intro _ ∘g det-nil
-- -- -- --     ; cons-case = det-cons-LinΣ
-- -- -- --     })

-- -- -- --   extract : ∀ q qs → q ∈-ε-closed qs → DetTrace qs ⊢ N.Parse q
-- -- -- --   extract q qs q∈qs = {!!}

-- -- -- --   witness : ∀ q →
-- -- -- --     N.Parse q ⊢ LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
-- -- -- --   witness q = N.recTrace (record
-- -- -- --     { the-ℓs = _
-- -- -- --     ; G = λ q → LinΣ[ qs ∈ ε-closed ] LinΣ[ q∈qs ∈ q ∈-ε-closed qs ] DetTrace qs
-- -- -- --     ; nil-case = λ is-acc →
-- -- -- --       LinΣ-intro (ε-closure N.isAcc)
-- -- -- --       ∘g LinΣ-intro (ε-closure-lift-∈ is-acc)
-- -- -- --       ∘g det-nil
-- -- -- --     ; cons-case = λ tr → ⊸-app ∘g ⊗-intro id (LinΣ-elim (λ qs → {!!}))
-- -- -- --     ; ε-cons-case = {!!}
-- -- -- --     })

-- -- -- --   -- -- TODO: perhaps prove this is a closure,
-- -- -- --   -- -- i.e. that the function is idempotent
-- -- -- --   -- ℙ-ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
-- -- -- --   -- ℙ-ε-closure X = FinSetDecℙ∃ N.Q N.Q X ε-reach

-- -- -- --   -- δFunN : ⟨ N.Q ⟩ → ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩
-- -- -- --   -- δFunN = N.hasTransition (isFinSet→Discrete isFinSetΣ₀)

-- -- -- --   -- data DetTrace : {!!} → Grammar (ℓ-suc ℓN) where
-- -- -- --   --   nil : ε ⊢ DetTrace {!!}

-- -- -- --   -- open DFA
-- -- -- --   -- ℙN : DFA {ℓ-suc ℓN}
-- -- -- --   -- ℙN .Q = FinSetDecℙ N.Q
-- -- -- --   -- ℙN .init = ε-reach N.init
-- -- -- --   -- ℙN .isAcc X =
-- -- -- --   --   DecProp∃
-- -- -- --   --     -- Quantifying over states in X : Σ[ q ∈ N .Q .fst ] X q .fst
-- -- -- --   --     (Decℙ→FinSet (N .Q) X)
-- -- -- --   --     -- Is any state in X accepting?
-- -- -- --   --     (λ x → LiftDecProp (N .isAcc (x .fst)))
-- -- -- --   -- ℙN .δ X c =
-- -- -- --   --   ε-closure (FinSetDecℙ∃ N.Q N.Q (ε-closure X) (flip δFunN c))


-- -- -- --   -- open N.Algebra
-- -- -- --   -- open N.AlgebraHom
-- -- -- --   -- NAlg : N.Algebra
-- -- -- --   -- NAlg .the-ℓs _ = ℓ-suc ℓN
-- -- -- --   -- NAlg .G q =
-- -- -- --   --   LinΣ[ X ∈ (Σ[ Y ∈ ⟨ ℙN.Q ⟩ ] Y q .fst .fst) ] ℙN.ParseFrom (X .fst)
-- -- -- --   -- NAlg .nil-case {q} qAcc _ pε = {!!}
-- -- -- --   -- NAlg .cons-case = {!!}
-- -- -- --   -- NAlg .ε-cons-case = {!!}

-- -- -- --   -- open LogicalEquivalence
-- -- -- --   -- N⊣⊢ℙN :
-- -- -- --   --   LogicalEquivalence N.InitParse ℙN.InitParse
-- -- -- --   -- N⊣⊢ℙN .fun = {!!}
-- -- -- --   -- N⊣⊢ℙN .inv = {!!}
