open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Determinization2 (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import Grammar.Inductive Alphabet as Inductive
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import NFA.Manual Alphabet
open import DFA Alphabet

open import Graph.Reachability
open import Helper

private
  variable
    ℓ ℓN : Level

open NFA

module _
  (N : NFA {ℓN})
  (isFinOrdStates : isFinOrd ⟨ N .Q ⟩)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  private
    module N = NFA N

  open directedGraph
  ε-graph : directedGraph ℓN
  ε-graph .states = N.Q
  ε-graph .directed-edges = N.ε-transition
  ε-graph .src = N.ε-src
  ε-graph .dst = N.ε-dst
  private module ε-graph = directedGraph ε-graph

  opaque
    ε-trans-from : Decℙ ⟨ N.Q ⟩ → Decℙ ⟨ N.ε-transition ⟩
    ε-trans-from X t = DecPropΣProp (Decℙ→FinSet N.Q X) (λ q →
      DecProp≡ (isFinSet→Discrete (str N.Q)) (N.ε-src t) (q .fst))
      (λ _ _ p q → Σ≡Prop (λ q → str (X q .fst)) (sym p ∙ q))

    ε-trans-into : Decℙ ⟨ N.Q ⟩ → Decℙ ⟨ N.ε-transition ⟩
    ε-trans-into X t = DecPropΣProp (Decℙ→FinSet N.Q X) (λ q →
      DecProp≡ (isFinSet→Discrete (str N.Q)) (N.ε-dst t) (q .fst))
      (λ _ _ p q → Σ≡Prop (λ q → str (X q .fst)) (sym p ∙ q))

  is-ε-closed : Decℙ ⟨ N.Q ⟩ → DecProp ℓN
  is-ε-closed X =
    DecProp∀ (Decℙ→FinSet N.ε-transition (ε-trans-into X)) (λ t →
      ε-trans-from X (t .fst))

  ε-closed : FinSet (ℓ-suc ℓN)
  ε-closed = FinSetSub (FinSetDecℙ N.Q) is-ε-closed

  ε-closed→Decℙ : ⟨ ε-closed ⟩ → Decℙ ⟨ N.Q ⟩
  ε-closed→Decℙ X = X .fst

  ε-closed→FinSet : ⟨ ε-closed ⟩ → FinSet ℓN
  ε-closed→FinSet X = Decℙ→FinSet N.Q (ε-closed→Decℙ X)

  -- there may be many accepting nodes
  -- so must be truncated so that it is a proposition
  hasAcc : ⟨ ε-closed ⟩ → DecProp ℓN
  hasAcc X = DecProp∃ (ε-closed→FinSet X) (λ q → N.isAcc (q .fst))

  -- hasAcc→accState :
  --   (X : ⟨ ε-closed ⟩) (hasAccX : ⟨ hasAcc X .fst ⟩) →
  --   Σ[ q ∈ ⟨ ε-closed→FinSet X ⟩ ] ⟨ N.isAcc (q .fst) .fst ⟩
  -- hasAcc→accState X hasAccX = {!!}

  -- ε-reach' : ⟨ N.Q ⟩ → Decℙ ⟨ N.Q ⟩
  -- ε-reach' q-start q-end .fst = _ , isPropPropTrunc
  -- ε-reach' q-start q-end .snd = DecReachable ε-graph q-end q-start

  -- opaque
  --   unfolding ε-trans-from ε-trans-into

  --   ε-reach'-is-ε-closed :
  --     (q-start : ⟨ N.Q ⟩) →
  --     ⟨ is-ε-closed (ε-reach' q-start) .fst ⟩
  --   ε-reach'-is-ε-closed q-start (t , (q , q-ε-reach) , dst-t≡q) .fst .fst = N.ε-src t
  --   ε-reach'-is-ε-closed q-start (t , (q , q-ε-reach) , dst-t≡q) .fst .snd = do
  --     (n , gw , q≡start-gw , q-start≡end-gw) ← q-ε-reach
  --     return (suc n , (ε-graph.cons t gw (dst-t≡q ∙ q≡start-gw)) , refl , q-start≡end-gw)
  --     where open PTMonad
  --   ε-reach'-is-ε-closed q-start (t , (q , q-ε-reach) , dst-t≡q) .snd = refl

  --   ε-closure : Decℙ ⟨ N.Q ⟩ → ⟨ ε-closed ⟩
  --   ε-closure X .fst = FinSetDecℙ∃ N.Q N.Q X ε-reach'
  --   ε-closure X .snd (t , _) .fst .fst = N.ε-src t
  --   ε-closure X .snd (t , (q , q-ε-reach) , dst-t≡q) .fst .snd = do
  --     (a , Xa , ε-reach-a) ← q-ε-reach
  --     return (a , (Xa , ε-reach'-is-ε-closed a (t , (q , ε-reach-a) , dst-t≡q) .fst .snd))
  --     where open PTMonad
  --   ε-closure X .snd t .snd = refl

  -- opaque
  --   ε-reach : ⟨ N.Q ⟩ → ⟨ ε-closed ⟩
  --   ε-reach q = ε-reach' q , ε-reach'-is-ε-closed q

  -- opaque
  --   lit-reach : ⟨ Alphabet ⟩ → ⟨ N.Q ⟩ → Decℙ ⟨ N.Q ⟩
  --   lit-reach c q-start = N.hasTransition (isFinSet→Discrete isFinSetAlphabet) q-start c

  --   lit-closure : ⟨ Alphabet ⟩ → Decℙ ⟨ N.Q ⟩ → Decℙ ⟨ N.Q ⟩
  --   lit-closure c X = FinSetDecℙ∃ N.Q N.Q X (lit-reach c)

  -- determinized : DFA
  -- determinized .DFA.Q = ε-closed
  -- determinized .DFA.init = ε-reach N.init
  -- determinized .DFA.isAcc X = LiftDecProp (hasAcc X)
  -- determinized .DFA.δ X c = ε-closure (lit-closure c (ε-closed→Decℙ X))

  -- private module D = DFA determinized

  -- NFA→DFA' : ∀ (q : ⟨ N.Q ⟩) →
  --  N.Parse q ⊢
  --    ⊕[ x ∈ ⟨ D.Q ⟩ ] D.Parse (ε-reach q) x
  -- NFA→DFA' = {!!}

  -- NFA→DFA : N.InitParse ⊢ D.InitParse
  -- NFA→DFA = NFA→DFA' N.init
  -- -- N.recInit (record
  -- --   { the-ℓs = λ _ → ℓ-suc ℓN
  -- --   ; G = λ q → D.InitParse
  -- --   ; nil-case = λ {q} q-is-acc → LinΣ-intro D.init ∘g LinΣ-intro {!!} ∘g D.nil
  -- --   ; cons-case = {!!}
  -- --   ; ε-cons-case = {!!}
  -- --   })

  -- -- DFA→NFA : D.InitParse ⊢ N.InitParse
  -- -- DFA→NFA = LinΣ-elim (λ X@(X' , X'-is-ε-closed) → LinΣ-elim (λ X-is-acc → D.recInit X (record
  -- --   { the-ℓs = λ _ → ℓN
  -- --   ; G = λ q → N.InitParse
  -- --   ; nil-case =
  -- --     let (q , x) = X in
  -- --     {!!}
  -- --   ; cons-case = λ q c → {!!}
  -- --   })))

  -- module Nondet where
  --   data Ctor {ℓ} : Type ℓ where
  --     [-] ∷ : Ctor

  --   data Side {ℓ} : Type ℓ where
  --     left right : Side

  --   endo : (G : Grammar ℓ) → Endofunctor ℓ
  --   endo G = ⊕e Ctor (λ where
  --     [-] → k G
  --     ∷ → &e Side (λ where
  --       left → Var
  --       right → Var))

  --   Nondet : (G : Grammar ℓ) → Grammar ℓ
  --   Nondet G = μ (endo G)

  --   Nondet-Algebra : (G : Grammar ℓ) → Grammar ℓ → Type ℓ
  --   Nondet-Algebra G = Inductive.Algebra (endo G)

  --   Nondet-rec : {G H : Grammar ℓ} → Nondet-Algebra G H → Nondet G ⊢ H
  --   Nondet-rec = Inductive.rec

  --   -- Ctor-[-] : {}

  --   bind : {G H : Grammar ℓ} → (G ⊢ Nondet H) → Nondet G ⊢ Nondet H
  --   bind f = Nondet-rec (λ w → λ where
  --     ([-] , x) → f w x
  --     --(∷ , x) → (roll ∘g (LinΣ-intro ∷ ∘g LinΠ-intro (λ { left → {!bind f!} ; right → {!!}}))) w x)
  --     (∷ , x) → {!!} w x)

  -- DFA→NFA : LinΣ[ q ∈ ⟨ D.Q ⟩ ] D.ParseFrom q ⊢ LinΣ[ q ∈ ⟨ N.Q ⟩ ] N.Parse q
  -- DFA→NFA = LinΣ-elim (λ qD-start →
  --   LinΣ-elim (λ qD-end → LinΣ-elim (λ qD-end-is-acc →
  --     D.recTrace qD-end (record
  --       { the-ℓs = λ _ → ℓN
  --       ; G = λ _ → LinΣ[ q ∈ ⟨ N.Q ⟩ ] N.Parse q
  --       ; nil-case =
  --         let (qN , qN-isAcc) = hasAcc→accState qD-end {!qD-end-is-acc!} in
  --         LinΣ-intro (qN .fst) ∘g {!N.nil!}
  --       ; cons-case = λ q c → {!!}
  --       }))))

  -- logicalEquivalence : isLogicallyEquivalent N.InitParse D.InitParse
  -- logicalEquivalence .fst = NFA→DFA
  -- logicalEquivalence .snd = {!!}

  -- weakEquivalence : isWeaklyEquivalent N.InitParse D.InitParse
  -- weakEquivalence = isLogicalEquivalence→WeakEquivalence _ _ logicalEquivalence
