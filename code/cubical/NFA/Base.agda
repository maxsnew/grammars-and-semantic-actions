open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.List hiding (init ; rec ; map)
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import Helper

private
  variable ℓN ℓN' ℓP ℓ : Level

record NFA ℓN : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN
    init : Q .fst
    isAcc : Q .fst → Bool
    transition : FinSet ℓN
    src : ⟨ transition ⟩ → ⟨ Q ⟩
    dst : ⟨ transition ⟩ → ⟨ Q ⟩
    label : ⟨ transition ⟩ → ⟨ Alphabet ⟩
    ε-transition : FinSet ℓN
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩

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
      ; (step t x) → ⊗e (k (literal* (label t))) (Var (dst t))
      ; (stepε t x) → Var (ε-dst t) }
    Trace : (q : ⟨ Q ⟩) → Grammar ℓN
    Trace = μ TraceTy

    STOP : ∀ {q} → true Eq.≡ isAcc q → ε ⊢ Trace q
    STOP acc = roll ∘g ⊕ᴰ-in (stop acc) ∘g liftG ∘g liftG

    STEP : ∀ t → literal (label t) ⊗ Trace (dst t) ⊢ Trace (src t)
    STEP t = roll ∘g ⊕ᴰ-in (step _ Eq.refl) ∘g (liftG ∘g liftG) ,⊗ liftG

    STEPε : ∀ t → Trace (ε-dst t) ⊢ Trace (ε-src t)
    STEPε t = roll ∘g ⊕ᴰ-in (stepε t Eq.refl) ∘g liftG

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
            ⊗e (k (LiftG ℓN (literal (label t)))) (Var (dst t)) }
      ; stepε → ⊕e (Eq.fiber ε-src q) λ { (t , Eq.refl) → Var (ε-dst t) } }

    Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓN
    Trace b = μ (TraceTy b)

    Parse : Grammar _
    Parse = Trace true init

    TraceAlg : Bool → (⟨ Q ⟩ → Grammar ℓ) → Type (ℓ-max ℓN ℓ)
    TraceAlg b = Algebra (TraceTy b)
