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
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet
import Cubical.Data.Equality as Eq
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

  data Tag (b : Bool) (q : ⟨ Q ⟩) : Type ℓN where
    stop : b Eq.≡ isAcc q → Tag b q
    step : ∀ t → (src t Eq.≡ q) → Tag b q
    stepε : ∀ t → (ε-src t Eq.≡ q) → Tag b q

  TraceTy : Bool → (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
  TraceTy b q = ⊕e (Tag b q) λ
    { (stop x) → k ε*
    ; (step t x) → ⊗e (k (literal* (label t))) (Var (dst t))
    ; (stepε t x) → Var (ε-dst t) }
  Trace : Bool → (q : ⟨ Q ⟩) → Grammar ℓN
  Trace b = μ (TraceTy b)

  STOP : ∀ {q} → ε ⊢ Trace (isAcc q) q
  STOP = roll ∘g ⊕ᴰ-in (stop Eq.refl) ∘g liftG ∘g liftG

  STEP : ∀ {b} t → literal (label t) ⊗ Trace b (dst t) ⊢ Trace b (src t)
  STEP t = roll ∘g ⊕ᴰ-in (step _ Eq.refl) ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPε : ∀ {b} t → Trace b (ε-dst t) ⊢ Trace b (ε-src t)
  STEPε t = roll ∘g ⊕ᴰ-in (stepε t Eq.refl) ∘g liftG

  Parse : Grammar _
  Parse = Trace true init

  TraceAlg = Algebra (TraceTy true)
