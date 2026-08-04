{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Automata.Implicit.RegExp (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum hiding (rec ; inl ; inr ; map)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Unambiguous Alphabet
open import Grammar.SequentialUnambiguity Alphabet
open import Automata.Implicit Alphabet public
open import Term Alphabet

open StrongEquivalence
open WeakEquivalence
open ImplicitDeterministicAutomaton

private
  variable
    ℓ ℓ' ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

module _
  (discAlpha : Discrete ⟨ Alphabet ⟩)
  where

  ⊥Aut : ImplicitDeterministicAutomaton ℓ-zero
  ⊥Aut .Q = Empty.⊥
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δq ()
  ⊥Aut .δᵢ _ = fail

  εAut : ImplicitDeterministicAutomaton ℓ-zero
  εAut .Q = Empty.⊥
  εAut .acc ()
  εAut .null = true
  εAut .δq ()
  εAut .δᵢ _ = fail

  module _ (c : ⟨ Alphabet ⟩) where

    litAut : ImplicitDeterministicAutomaton ℓ-zero
    litAut .Q = Unit
    litAut .acc _ = true
    litAut .null = false
    litAut .δᵢ c' =
      decRec
        (λ _ → ↑f _)
        (λ _ → fail)
        (discAlpha c c')
    litAut .δq _ _ = fail

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjointFirsts :
      ∀ (c : ⟨ Alphabet ⟩) →
      (fail ≡ M .δᵢ c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    ⊕Aut : ImplicitDeterministicAutomaton (ℓ-max ℓ ℓ')
    ⊕Aut .Q = M .Q ⊎ M' .Q
    ⊕Aut .acc (Sum.inl q) = M .acc q
    ⊕Aut .acc (Sum.inr q') = M' .acc q'
    ⊕Aut .null =
      Sum.rec
        (λ _ → M' .null)
        (λ _ → M .null)
        notBothNull
    ⊕Aut .δq (Sum.inl q) c = mapFreelyAddFail Sum.inl (M .δq q c)
    ⊕Aut .δq (Sum.inr q') c = mapFreelyAddFail Sum.inr (M' .δq q' c)
    ⊕Aut .δᵢ c =
      Sum.rec
        (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
        (λ _ → mapFreelyAddFail Sum.inl (M .δᵢ c))
        (disjointFirsts c)

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notNullM : (M .null ≡ false))
    (seqUnambig :
      ∀ (c : ⟨ Alphabet ⟩) →
      (∀ (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    ⊗Aut : ImplicitDeterministicAutomaton (ℓ-max ℓ ℓ')
    ⊗Aut .Q = M .Q ⊎ M' .Q
    ⊗Aut .acc (Sum.inl q) = M .acc q and M' .null
    ⊗Aut .acc (Sum.inr q') = M' .acc q'
    ⊗Aut .null = false
    ⊗Aut .δq (Sum.inl q) c =
      if (M .acc q)
      then
        (Sum.rec
          (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
          (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
          (seqUnambig c))
      else mapFreelyAddFail Sum.inl (M .δq q c)
    ⊗Aut .δq (Sum.inr q') c = mapFreelyAddFail Sum.inr (M' .δq q' c)
    ⊗Aut .δᵢ c = mapFreelyAddFail Sum.inl (M .δᵢ c)

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (notNullM : (M .null ≡ false))
    (seqUnambig :
      ∀ (c : ⟨ Alphabet ⟩) →
      (∀ (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M .δᵢ c)
    )
    where

    *Aut : ImplicitDeterministicAutomaton ℓ
    *Aut .Q = M .Q
    *Aut .acc q = M .acc q
    *Aut .null = true
    *Aut .δq q c =
      if (M .acc q)
      then
        (Sum.rec
          (λ _ → M .δᵢ c)
          (λ _ → M .δq q c)
          (seqUnambig c))
      else M .δq q c
    *Aut .δᵢ c = M .δᵢ c
