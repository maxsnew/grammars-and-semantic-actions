open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automata.Deterministic.Rev (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Parser Alphabet
open import Term Alphabet

private
  variable
    ℓ ℓ' : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  -- Forward
  data FwdTag (q : Q) : Type ℓ where
    start : q Eq.≡ init → FwdTag q
    step : ∀ (c : ⟨ Alphabet ⟩) q' → (δ q' c Eq.≡ q) → FwdTag q

  FwdTraceF : Q → Functor Q
  FwdTraceF q = ⊕e (FwdTag q) λ where
    (start Eq.refl) → k ε*
    (step c q' δq'c≡q) → Var q' ⊗e k (literal* c)

  module _ {X : Q → Grammar ℓ'} (ϕ : Algebra FwdTraceF X) where
    fwd-run : string ⊢ ⊕[ q ∈ Q ] X q
    fwd-run = fold*l _
      (σ init ∘g ϕ init ∘g σ (start Eq.refl) ∘g liftG ∘g liftG)
      (⊕ᴰ-elim (λ q' → (⊕ᴰ-elim λ c →
        σ (δ q' c) ∘g ϕ _ ∘g σ (step c q' Eq.refl) ∘g liftG ,⊗ (liftG ∘g liftG))
      ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
      ∘g ⊕ᴰ-distL .StrongEquivalence.fun)

  data BwdTag (b : Bool)(q : Q) : Type ℓ where
    stop : isAcc q Eq.≡ b → BwdTag b q
    step : ⟨ Alphabet ⟩ → BwdTag b q
  BwdTraceF : Bool → Q → Functor (Bool × Q)
  BwdTraceF q = ? -- ⊕e (BwdTag q) λ where
    -- (stop isAcc-q) → k ε*
    -- (step c) → k (literal* c) ⊗e Var (δ q c)

  module _ {X : Q → Grammar ℓ'} (ϕ : Algebra BwdTraceF X) where
    rev-run : Algebra FwdTraceF λ qₑ → {!X !}
    rev-run = {!!}

  data Tag : Type ℓ where
    stop step : Tag

  open Iso

  TagRep : Iso Tag Bool
  TagRep = iso
    (λ { stop → false ; step → true})
    (λ { false → stop ; true → step})
    (λ { false → refl ; true → refl})
    (λ { stop → refl ; step → refl})

  isSetTag : isSet Tag
  isSetTag = isSetRetract (TagRep .fun) (TagRep .inv) (TagRep .leftInv) isSetBool

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → (k (literal* c)) ⊗e (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

