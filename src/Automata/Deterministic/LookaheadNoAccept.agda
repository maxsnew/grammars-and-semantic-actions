-- Deterministic automaton that can use one token of lookahead to disambiguate
-- This version is just a pure transition system, with no notion of initial or accepting state
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automata.Deterministic.LookaheadNoAccept (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Parser Alphabet
open import Term Alphabet

private
  variable
    ℓ ℓ' ℓ'' : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    δ : Q → ⟨ Alphabet ⟩ → Maybe ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop : Tag
    step : ⟨ Alphabet ⟩ → Maybe ⟨ Alphabet ⟩ → Tag

  module _ where
    open import Cubical.Data.Unit
    open import Cubical.Data.Sum as Sum
    isSetTag : isSet Tag
    isSetTag = isSetRetract {B = Unit ⊎ (⟨ Alphabet ⟩ × Maybe ⟨ Alphabet ⟩)}
      (λ { stop → Sum.inl _ ; (step c g) → Sum.inr (c , g) })
      (λ { (_⊎_.inl x) → stop ; (_⊎_.inr x) → step (x .fst) (x .snd) })
      (λ { stop → refl ; (step x x₁) → refl })
      (isSet⊎ isSetUnit (isSet× (Alphabet .snd) (isOfHLevelMaybe 0 (Alphabet .snd))))

  TraceF : (q : Q) → Functor Q
  TraceF q = ⊕e Tag λ where
    stop → k ε*
    (step c g) → k (literal* c) ⊗e (Var (δ q c g) &e2 k (LiftG _ (PeekChar g)))
  
  Trace : (q : Q) → Grammar ℓ
  Trace = μ TraceF

  module _ {X : Q → Grammar ℓ'}(ϕ : Algebra TraceF X) where
    parse-alg : string ⊢ &[ q ∈ Q ] X q
    parse-alg = fold*r char
      (&ᴰ-intro λ q → ϕ q ∘g σ stop ∘g liftG ∘g liftG)
      (&ᴰ-intro λ q →
        (⊕ᴰ-elim λ c →
          (⊕ᴰ-elim λ g →
            ϕ q
            ∘g σ (step c g)
            ∘g (liftG ∘g liftG) ,⊗ ((liftG ∘g π (δ q c g)) ,&p (liftG ∘g liftG)))
          ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ peek .StrongEquivalence.fun)
        ∘g ⊕ᴰ-distL .StrongEquivalence.fun)
