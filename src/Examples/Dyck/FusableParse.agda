{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck.FusableParse where

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

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Literal Alphabet
open import Grammar.String.Liftless Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Inductive.Liftless.Indexed Alphabet
open import Grammar.Inductive.Liftless.Structure Alphabet
open import Term Alphabet

open import Examples.Dyck.Grammar
open import Automata.Deterministic.FusableParse Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' : Level

CountParens : DeterministicAutomaton (Maybe ℕ)
CountParens .DeterministicAutomaton.init = just 0
CountParens .DeterministicAutomaton.isAcc nothing = false
CountParens .DeterministicAutomaton.isAcc (just zero) = true
CountParens .DeterministicAutomaton.isAcc (just (suc n)) = false
CountParens .DeterministicAutomaton.δ nothing c = nothing
CountParens .DeterministicAutomaton.δ (just n) [ = just (suc n)
CountParens .DeterministicAutomaton.δ (just zero) ] = nothing
CountParens .DeterministicAutomaton.δ (just (suc n)) ] = just n

private
  module CountParens = DeterministicAutomaton CountParens
module _ where
  Closers : ℕ → Functor Unit
  Closers zero = k ε
  Closers (suc n) = k (literal RP) ⊗e Var _ ⊗e Closers n

  Ix-f : (Bool × Maybe ℕ) → Functor (Unit)
  Ix-f (false , n?) = k (CountParens.Trace false n?)
  Ix-f (true , nothing) = ⊕e Empty.⊥ λ ()
  Ix-f (true , just n)    = Var _ ⊗e Closers n

  module _ (A : Unit → Grammar ℓ-zero) (α : Algebra DyckF A) where
    step-[ : ∀ n →
      (literal [) ⊗ (⟦ Ix-f (true , just (suc n)) ⟧ A)
      ⊢ ⟦ Var tt ⊗e Closers n ⟧ A
    step-[ _ = (α _ ∘g σ balanced') ,⊗ id ∘g ⊗-assoc4

    Str-f : Algebra CountParens.TraceF (λ bn? → ⟦ Ix-f bn? ⟧ A )
    -- TODO: this could be done entirely generically for DeterministicAutomaton
    Str-f (false , q) = ⊕ᴰ-elim (λ where
      (CountParens.stop x) → roll ∘g σ (CountParens.stop x)
      (CountParens.step x) → roll ∘g σ (CountParens.step x))
    -- TODO: this could be done generically if we made δ : State → Alphabet → Maybe State
    Str-f (true , nothing) = ⊕ᴰ-elim (λ where
      (CountParens.step c) → ⊕ᴰ-elim (λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    -- This is specific to LL grammars
    Str-f (true , just zero) = ⊕ᴰ-elim (λ where
      -- interesting: the nil case is the same as the close case for the other state...
      (CountParens.stop _) → (α _ ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻
      (CountParens.step [) → step-[ zero
      (CountParens.step ]) → (⊕ᴰ-elim λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    Str-f (true , just (suc n)) = ⊕ᴰ-elim (λ where
      (CountParens.step [) → step-[ $ suc n
      (CountParens.step ]) → (α _ ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻) -- (α _ ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻

  opaque
    unfolding ⊗-intro ⊕ᴰ-distR ⊗-unit-l⁻
    Str-f-homo : ∀ {A B α β}
      (ϕ : Homomorphism DyckF α β)
      → isHomo CountParens.TraceF (Str-f A α) (Str-f B β) λ bn? → map (Ix-f bn?) (ϕ .fst)
    Str-f-homo ϕ (false , q) = ⊕ᴰ≡ _ _ λ where
      (CountParens.stop x) → refl
      (CountParens.step x) → refl
    Str-f-homo ϕ (true , nothing) = ⊕ᴰ≡ _ _ λ where
      (CountParens.step c) → λ i → {!!}
    Str-f-homo ϕ (true , just zero) = ⊕ᴰ≡ _ _ λ where
      (CountParens.stop _) → λ i → (ϕ .snd _ i ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻
      (CountParens.step [) → λ i → (ϕ .snd _ i ∘g σ balanced') ,⊗ id ∘g ⊗-assoc4
      (CountParens.step ]) → {!!} -- contradiction
    Str-f-homo ϕ (true , just (suc n)) = ⊕ᴰ≡ _ _ λ where
      (CountParens.step [) → {!λ i → (ϕ .snd _ i ∘g σ balanced') ,⊗ id ∘g ⊗-assoc4!}
      (CountParens.step ]) → λ i → {!ϕ .snd _ i ,⊗ id ∘g ⊗-unit-l⁻!} 
      
--   -- TODO: generic
--     Str-f (false , n?) = {!!}
--   -- TODO: the following could be generic if we had a notion of deterministic automaton with implicit failure state
--     Str-f (true , nothing) = ⊕ᴰ-elim (λ where
--       (CountParens.step x) →
--         ⊕ᴰ-elim (λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ lowerG)
--     Str-f (true , just zero) = ⊕ᴰ-elim λ where
--       (CountParens.stop Eq.refl) → (liftG ∘g ϕ _ ∘g σ nil' ∘g liftG) ,⊗ id ∘g ⊗-unit-l⁻
--       (CountParens.step [) → step-f zero -- step-f zero c
--       (CountParens.step ]) → (⊕ᴰ-elim λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ lowerG
--     Str-f (true , just (suc n)) = ⊕ᴰ-elim λ where
--       (CountParens.step [) → step-f (suc n) -- step-f zero c
--       (CountParens.step ]) → (liftG ∘g ϕ _ ∘g σ nil' ∘g liftG) ,⊗ {!!} ∘g ⊗-unit-l⁻ -- step-f zero c

Trace→Dyck : StructureTransform
  CountParens.TraceStructure
  DyckStr
Trace→Dyck = record { Ix-f = Ix-f ; Str-f = Str-f ; Str-f-homo = {!!} }
