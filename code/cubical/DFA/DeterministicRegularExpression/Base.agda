open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module DFA.DeterministicRegularExpression.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.More
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Bool.More
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Maybe.PartialFunction

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import DFA.Base Alphabet public
open import Term Alphabet

open DeterministicAutomaton

private
  variable
    ℓ ℓ' : Level

  mkFinSet : {A : Type ℓ} → isFinSet A → FinSet ℓ
  mkFinSet {A = A} _ .fst = Maybe (Unit ⊎ A) -- inl is the initial state
  mkFinSet isFinSetA .snd = isFinSetMaybe (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSetA))

open ImplicitDeterministicAutomaton
open LogicalEquivalence

module _
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  ⊥Aut : ImplicitDeterministicAutomaton Empty.⊥
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δ₀ _ _ = nothing

  ⊥DFA : DFAOver (mkFinSet isFinSet⊥)
  ⊥DFA = Aut ⊥Aut

  ⊥DFA≅ : Trace ⊥DFA true nothing ≅ ⊥
  ⊥DFA≅ =
    ≈→≅
      (unambiguous-Trace ⊥DFA true nothing)
      unambiguous⊥
      (mkLogEq
        {!!}
        ⊥-elim
      )
    where
    ⊥Alg : {!TraceAlg ⊥DFA (λ _ → ⊥)!}
    ⊥Alg nothing = {!!}
    -- ⊕ᴰ-elim λ { stop → ⊕ᴰ-elim λ {()} ; step → {!!}}
    ⊥Alg (just x) = {!!}

  εAut : ImplicitDeterministicAutomaton Empty.⊥
  εAut .acc ()
  εAut .null = true
  εAut .δ₀ _ _ = nothing

  εDFA : DFAOver (mkFinSet isFinSet⊥)
  εDFA = Aut εAut

  litAut : ⟨ Alphabet ⟩ → ImplicitDeterministicAutomaton Unit
  litAut c .acc _ = true
  litAut c .null = false
  litAut c .δ₀ (inl _) c' =
    decRec
      (λ _ → just _)
      (λ _ → nothing)
      (DiscreteAlphabet isFinSetAlphabet c c')
  litAut c .δ₀ (inr q) _ = nothing

  litDFA : ⟨ Alphabet ⟩ → DFAOver (mkFinSet isFinSetUnit)
  litDFA c = Aut (litAut c)

  module _
    {Q : FinSet ℓ}
    {Q' : FinSet ℓ'}
    (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
    (M' : ImplicitDeterministicAutomaton ⟨ Q' ⟩)
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjoint-firsts : disjointDomains (M .δ₀ (inl _)) (M' .δ₀ (inl _)))
    where
    ⊕Aut : ImplicitDeterministicAutomaton (⟨ Q ⟩ ⊎ ⟨ Q' ⟩)
    ⊕Aut .acc (inl q) = M .acc q
    ⊕Aut .acc (inr q') = M' .acc q'
    ⊕Aut .null = M .null or M' .null
    ⊕Aut .δ₀ (inl _) =
      union⊎
        (M .δ₀ (inl _)) (M' .δ₀ (inl _))
        disjoint-firsts
    ⊕Aut .δ₀ (inr (inl q)) c = map-Maybe inl (M .δ₀ (inr q) c)
    ⊕Aut .δ₀ (inr (inr q')) c = map-Maybe inr (M' .δ₀ (inr q') c)

    ⊕DFA : DFAOver (mkFinSet (isFinSet⊎ Q Q'))
    ⊕DFA = Aut ⊕Aut

  module _
    {Q : FinSet ℓ}
    {Q' : FinSet ℓ'}
    (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
    (M' : ImplicitDeterministicAutomaton ⟨ Q' ⟩)
    (notNullM : M .null ≡ false)
    (seq-unambig :
      ∀ (q : ⟨ Q ⟩) →
      M .acc q ≡ true →
      disjointDomains (M .δ₀ (inr q)) (M' .δ₀ (inl _)))
    where

    ⊗Aut : ImplicitDeterministicAutomaton (⟨ Q ⟩ ⊎ ⟨ Q' ⟩)
    ⊗Aut .acc (inl q) = if M' .null then M .acc q else false
    ⊗Aut .acc (inr q') = M' .acc q'
    ⊗Aut .null = false
    ⊗Aut .δ₀ (inl _) c = map-Maybe inl (M .δ₀ (inl _) c)
    ⊗Aut .δ₀ (inr (inl q)) =
      if' M .acc q then
        (λ qIsAcc → union⊎ (M .δ₀ (inr q)) (M' .δ₀ (inl _)) (seq-unambig q qIsAcc))
        else
        (λ _ →
          (λ c → map-Maybe inl (M .δ₀ (inr q) c))
        )
    ⊗Aut .δ₀ (inr (inr q')) c = map-Maybe inr (M' .δ₀ (inr q') c)

    ⊗DFA : DFAOver (mkFinSet (isFinSet⊎ Q Q'))
    ⊗DFA = Aut ⊗Aut

  module _
    {Q : FinSet ℓ}
    (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
    (notNullM : M .null ≡ false)
    (seq-unambig :
      ∀ (q : ⟨ Q ⟩) →
      M .acc q ≡ true →
      disjointDomains (M .δ₀ (inr q)) (M .δ₀ (inl _)))
    where

    *Aut : ImplicitDeterministicAutomaton ⟨ Q ⟩
    *Aut .acc = M .acc
    *Aut .null = true
    *Aut .δ₀ (inl _) = M .δ₀ (inl _)
    *Aut .δ₀ (inr q) =
      if' M .acc q then
        (λ qIsAcc → union (M .δ₀ (inr q)) (M .δ₀ (inl _)) (seq-unambig q qIsAcc))
        else
        (λ _ → M .δ₀ (inr q))

    *DFA : DFAOver (mkFinSet (Q .snd))
    *DFA = Aut *Aut
