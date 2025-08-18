{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck.Grammars where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Examples.Dyck.Alphabet

open import Grammar Alphabet hiding (_+)
open import Parser Alphabet
open import Term Alphabet
open import Automata.Deterministic Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' : Level

module ParseTree where
  data DyckTag : Type ℓ-zero where
    nil' balanced' : DyckTag

  isSetDyckTag : isSet DyckTag
  isSetDyckTag = isSetRetract enc dec retr isSetBool where
    enc : DyckTag → Bool
    enc nil' = false
    enc balanced' = true
    dec : Bool → DyckTag
    dec false = nil'
    dec true = balanced'
    retr : (x : DyckTag) → dec (enc x) ≡ x
    retr nil' = refl
    retr balanced' = refl

  -- | data Dyck (x : Unit) : L where
  -- |   nil : ↑ Dyck x
  -- |   balanced : ↑ (literal LP ⊗ Dyck x ⊗ literal RP ⊗ Dyck x)
  DyckF : Unit → Functor Unit
  DyckF _ = ⊕e DyckTag (λ
    { nil' → k ε
    ; balanced' → (k (literal [)) ⊗e (Var _) ⊗e (k (literal ]) ⊗e (Var _)) })

module Aut where
  Dyck : DeterministicAutomaton (Maybe ℕ)
  Dyck .DeterministicAutomaton.init = just 0
  Dyck .DeterministicAutomaton.isAcc nothing = false
  Dyck .DeterministicAutomaton.isAcc (just zero) = true
  Dyck .DeterministicAutomaton.isAcc (just (suc n)) = false
  Dyck .DeterministicAutomaton.δ nothing c = nothing
  Dyck .DeterministicAutomaton.δ (just n) [ = just (suc n)
  Dyck .DeterministicAutomaton.δ (just zero) ] = nothing
  Dyck .DeterministicAutomaton.δ (just (suc n)) ] = just n

  module _ {X : Grammar ℓ} (ϕ : Algebra ParseTree.DyckF (λ _ → X)) where
    X' : Bool → Maybe ℕ → Grammar ℓ
    X' false _ = ⊤*
    X' true nothing = ⊥*
    X' true (just zero) = X
    X' true (just (suc n)) = X ⊗ literal RP ⊗ X' true (just n)

    mkTreeAlg : ∀ b → Algebra (DeterministicAutomaton.TraceTy Dyck b) (X' b)
    mkTreeAlg false = λ _ → ⊤*-intro
    mkTreeAlg true nothing = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim (λ where
        (lift [) → ⊗⊥* ∘g id ,⊗ lowerG
        (lift ]) → ⊗⊥* ∘g id ,⊗ lowerG))
    mkTreeAlg true (just zero) = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim (λ _ → ϕ _ ∘g σ ParseTree.nil' ∘g mapLift lowerG)
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim (λ where
        (lift [) → ϕ _ ∘g σ ParseTree.balanced' ∘g mapLift lowerG ,⊗ (liftG ,⊗ liftG ,⊗ liftG ∘g lowerG)
        (lift ]) → ⊗⊥* ∘g id ,⊗ lowerG))
    mkTreeAlg true (just (suc n)) = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim (λ ())
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim (λ where
        (lift [) → (ϕ _ ∘g σ ParseTree.balanced' ∘g mapLift id ,⊗ liftG ,⊗ liftG ,⊗ liftG ∘g ⊗-assoc⁻3) ,⊗ id ∘g ⊗-assoc ∘g ⊗-assoc ∘g lowerG ,⊗ (⊗-assoc ∘g lowerG)
        (lift ]) → (ϕ _ ∘g σ ParseTree.nil' ∘g liftG) ,⊗ (lowerG ∘g lowerG) ,⊗ lowerG ∘g ⊗-unit-l⁻))

parse : string ⊢ μ ParseTree.DyckF _ ⊕ ⊤
parse = (⊕ᴰ-elim λ where
  false → inr ∘g ⊤-intro
  true → inl)
  ∘g π (just 0)
  ∘g DeterministicAutomaton.de-forested-parse Aut.Dyck _ (Aut.mkTreeAlg (initialAlgebra ParseTree.DyckF))
