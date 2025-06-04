-- Deterministic automaton that can use one token of lookahead to disambiguate
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automata.Deterministic.Lookahead (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_)
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
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Maybe ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop step : Tag

  TagRep : Iso Tag Bool
  TagRep = iso
    (λ { stop → false ; step → true})
    (λ { false → stop ; true → step})
    (λ { false → refl ; true → refl})
    (λ { stop → refl ; step → refl})

  isSetTag : isSet Tag
  isSetTag = isSetRetract (TagRep .Iso.fun) (TagRep .Iso.inv) (TagRep .Iso.leftInv) isSetBool

  TraceF : Bool → (q : Q) → Functor Q
  TraceF b q = ⊕e Tag λ where
    stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
    step → ⊕e (Lift (⟨ Alphabet ⟩ × Maybe ⟨ Alphabet ⟩)) λ { (lift (c , g)) →
      k (literal* c) ⊗e (Var (δ q c g) &e2 k (LiftG _ (PeekChar g))) }

  
  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceF b)

  STEP : ∀ c g b q → ＂ c ＂ ⊗ (Trace b (δ q c g) & PeekChar g) ⊢ Trace b q
  STEP c g b q = roll ∘g σ step ∘g σ (lift (c , g)) ∘g (liftG ∘g liftG) ,⊗ liftG ,&p (liftG ∘g liftG)

  parse : string ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
  parse =
    fold*r char
      (&ᴰ-intro (λ q → σ (isAcc q) ∘g roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG))
      (&ᴰ-intro (λ q → (⊕ᴰ-elim λ c → ((⊕ᴰ-elim λ g →
          (map⊕ᴰ (λ b → STEP c g b q)
          ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ &⊕ᴰ-distL≅ .StrongEquivalence.fun) ∘g id ,⊗ π (δ q c g) ,&p id)
        ∘g ⊕ᴰ-distR .StrongEquivalence.fun) ∘g id ,⊗ peek .StrongEquivalence.fun)
        ∘g ⊕ᴰ-distL .StrongEquivalence.fun))


  module _ {X : Bool → Q → Grammar ℓ'}(ϕ : ∀ b → Algebra (TraceF b) (X b)) where
    parse-alg : string ⊢ &[ q ∈ Q ] ⊕[ b ∈ Bool ] X b q
    parse-alg = fold*r char
      (&ᴰ-intro λ q → σ (isAcc q) ∘g ϕ (isAcc q) q ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG)
      (&ᴰ-intro λ q →
        (⊕ᴰ-elim λ c →
          (⊕ᴰ-elim λ g →
            map⊕ᴰ (λ b → ϕ b q ∘g σ step ∘g σ (lift (c , g)) ∘g (liftG ∘g liftG) ,⊗ liftG ,&p (liftG ∘g liftG))
            ∘g ⊕ᴰ-distR .StrongEquivalence.fun
            ∘g id ,⊗ (&⊕ᴰ-distL≅ .StrongEquivalence.fun ∘g π (δ q c g) ,&p id))
          ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ peek .StrongEquivalence.fun)
        ∘g ⊕ᴰ-distL .StrongEquivalence.fun)
