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
open import Cubical.Data.List hiding (init ; rec)

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

  TraceAlg = Algebra TraceTy

  module _ {ℓP}(P : Grammar ℓP) where
    L = ℓ-max ℓP ℓN
    Q' = Lift {j = L} ⟨ Q ⟩

    Tag' : Q' → Type L
    Tag' q = Lift {j = L} (Tag (lower q))

    TraceTy' : (q : Q')  → Functor Q'
    TraceTy' (lift q) = LiftFunctor ⟨ Q ⟩ (TraceTy q)

    PAlgTy : (q : Q') → Functor Q'
    PAlgTy q = ⊕e (Tag' q) λ
      { (lift (stop x)) → k (LiftG ℓN P)
      ; (lift (step t x)) →
        ⊗e (k (literal* (label t))) (Var (lift (dst t)))
      ; (lift (stepε t x)) → Var (lift (ε-dst t)) }

    PAlgebra : (g :  Q' → Grammar L) → Type L
    PAlgebra = Algebra PAlgTy

    initialPAlg : PAlgebra (μ PAlgTy)
    initialPAlg = initialAlgebra PAlgTy

    module _ (g :  Q' → Grammar L) (pAlg : PAlgebra g) where
      underlyingAlg : Algebra TraceTy' (λ q → g q ⟜ P)
      underlyingAlg q = ⊕ᴰ-elim (λ {
          (lift (stop acc)) →
            ⟜-intro
              ((pAlg q
              ∘g ⊕ᴰ-in (lift (stop acc)))
              ∘g liftG ∘g liftG
              ∘g ⊗-unit-l)
             ∘g lowerG ∘g lowerG ∘g lowerG
        ; (lift (step t Eq.refl)) →
          ⟜-intro
            (pAlg q
            ∘g ⊕ᴰ-in (lift (step t Eq.refl))
            ∘g id ,⊗ ⟜-app ∘g ⊗-assoc⁻
            ∘g ((liftG ∘g liftG) ,⊗ ⟜-mapCod liftG) ,⊗ id)
            ∘g (lowerG ∘g lowerG ∘g lowerG) ,⊗ lowerG
        ; (lift (stepε t Eq.refl)) →
          ⟜-intro (
            pAlg q
            ∘g ⊕ᴰ-in (lift (stepε t Eq.refl))
            ∘g liftG ∘g ⟜-app)
          ∘g lowerG
          })

      -- curryPAlg :
      --   Homomorphism PAlgTy initialPAlg pAlg →
      --   Homomorphism TraceTy (initialAlgebra TraceTy) underlyingAlg
      -- curryPAlg e .fst q =
      --   ⟜-intro (
      --     e .fst (lift q)
      --     ∘g {!⟜-intro⁻ (rec _ underlyingAlg q)!})
      -- curryPAlg e .snd = {!!}
