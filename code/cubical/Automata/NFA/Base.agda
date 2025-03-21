open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module Automata.NFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.List hiding (init ; rec ; map)
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

private
  variable ℓN ℓN' ℓP ℓ : Level

record NFA ℓN : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN -- finite set of states
    init : ⟨ Q ⟩  -- initial state
    isAcc : ⟨ Q ⟩ → Bool -- acceptance for states
    transition : FinSet ℓN -- finite set of transitions
    src : ⟨ transition ⟩ → ⟨ Q ⟩ -- source state of transition
    dst : ⟨ transition ⟩ → ⟨ Q ⟩ -- destination state of transition
    label : ⟨ transition ⟩ → ⟨ Alphabet ⟩ -- label of transition
    ε-transition : FinSet ℓN -- finite set of ε transitions
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩ -- source of ε transition
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩ -- destination of ε transition

  decEqQ : Discrete ⟨ Q ⟩
  decEqQ = isFinSet→Discrete (str Q)

  matchesTransition :
    Discrete ⟨ Alphabet ⟩ →
    ⟨ transition ⟩ →
    ⟨ Q ⟩ →
    ⟨ Alphabet ⟩ →
    ⟨ Q ⟩ → DecProp ℓN
  matchesTransition discAlphabet t src' label' dst' =
     DecProp×
         (DecProp≡ (discreteLift {L' = ℓN} discAlphabet)
           (lift label') (lift (label t)))
         (DecProp×
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift src') (lift (src t)))
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift dst') (lift (dst t)))
          )

  hasTransition : Discrete ⟨ Alphabet ⟩ → ⟨ Q ⟩ →
    ⟨ Alphabet ⟩ → ⟨ Q ⟩ → DecProp ℓN
  hasTransition discAlphabet src' label' dst' =
    DecProp∃ transition (λ t →
      matchesTransition discAlphabet t src' label' dst')

  module Accepting where
    data Tag (q : ⟨ Q ⟩) : Type ℓN where
      stop : true Eq.≡ isAcc q → Tag q
      step : ∀ t → (src t Eq.≡ q) → Tag q
      stepε : ∀ t → (ε-src t Eq.≡ q) → Tag q

    TraceTy : (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
    TraceTy q = ⊕e (Tag q) λ
      { (stop x) → k ε*
      ; (step t x) → (k (literal* (label t))) ⊗e (Var (dst t))
      ; (stepε t x) → Var (ε-dst t) }
    Trace : (q : ⟨ Q ⟩) → Grammar ℓN
    Trace = μ TraceTy

    STOP : ∀ {q} → true Eq.≡ isAcc q → ε ⊢ Trace q
    STOP acc = roll ∘g σ (stop acc) ∘g liftG ∘g liftG

    STEP : ∀ t → literal (label t) ⊗ Trace (dst t) ⊢ Trace (src t)
    STEP t = roll ∘g σ (step _ Eq.refl) ∘g (liftG ∘g liftG) ,⊗ liftG

    STEPε : ∀ t → Trace (ε-dst t) ⊢ Trace (ε-src t)
    STEPε t = roll ∘g σ (stepε t Eq.refl) ∘g liftG

    Parse : Grammar _
    Parse = Trace init

    TraceAlg : (⟨ Q ⟩ → Grammar ℓ) → Type (ℓ-max ℓN ℓ)
    TraceAlg = Algebra TraceTy

  module PotentiallyRejecting where
    data Tag : Type ℓN where
        stop step stepε : Tag

    TraceTy : Bool → (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
    TraceTy b q = ⊕e Tag λ {
        stop → ⊕e (Lift (b Eq.≡ isAcc q)) (λ
          (lift acc) → k (LiftG ℓN ε) )
      ; step → ⊕e (Eq.fiber src q) λ {
          (t , Eq.refl ) →
            (k (LiftG ℓN (literal (label t)))) ⊗e (Var (dst t)) }
      ; stepε → ⊕e (Eq.fiber ε-src q) λ { (t , Eq.refl) → Var (ε-dst t) } }

    Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓN
    Trace b = μ (TraceTy b)

    Parse : Grammar _
    Parse = Trace true init

    TraceAlg : Bool → (⟨ Q ⟩ → Grammar ℓ) → Type (ℓ-max ℓN ℓ)
    TraceAlg b = Algebra (TraceTy b)
