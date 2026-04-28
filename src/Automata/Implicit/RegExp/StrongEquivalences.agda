{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Automata.Implicit.RegExp.StrongEquivalences (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum hiding (rec ; inl ; inr ; map)
open import Cubical.Data.Bool hiding (_⊕_)

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Unambiguous Alphabet
open import Grammar.SequentialUnambiguity Alphabet
open import Automata.Implicit.RegExp Alphabet
open import Automata.Implicit.RegExp.WeakEquivalences Alphabet
open import Term Alphabet

open StrongEquivalence
open ImplicitDeterministicAutomaton

private
  variable
    ℓ ℓ' : Level

module _
  (discAlpha : Discrete ⟨ Alphabet ⟩)
  where

  ⊥≅ : Parse (⊥Aut discAlpha) ≅ ⊥
  ⊥≅ =
    ≈→≅
      (unambiguous-Trace (⊥Aut discAlpha) true _)
      unambiguous⊥
      (⊥≈ discAlpha)

  ε≅ : Parse (εAut discAlpha) ≅ ε
  ε≅ =
    ≈→≅
      (unambiguous-Trace (εAut discAlpha) true _)
      unambiguousε
      (ε≈ discAlpha)

  module _ (c : ⟨ Alphabet ⟩) where

    lit≅ : Parse (litAut discAlpha c) ≅ ＂ c ＂
    lit≅ =
      ≈→≅
        (unambiguous-Trace (litAut discAlpha c) true _)
        (unambiguous-literal c)
        (lit≈ discAlpha c)

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjointFirsts :
      ∀ (c : ⟨ Alphabet ⟩) →
      (fail ≡ M .δᵢ c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    private
      ⊕A = ⊕Aut discAlpha M M' notBothNull disjointFirsts

      disjointParses : disjoint (Parse M) (Parse M')
      disjointParses =
        #→disjoint
          (λ c →
            Sum.map
              (¬FirstAut M c)
              (¬FirstAut M' c)
              (disjointFirsts c)
          )
          (Sum.map
            (¬NullableAut M)
            (¬NullableAut M')
            notBothNull
          )

    ⊕Aut≅ : Parse ⊕A ≅ Parse M ⊕ Parse M'
    ⊕Aut≅ =
      ≈→≅
        (unambiguous-Trace ⊕A true _)
        (unambiguous⊕
          (unambiguous-Trace M  true _)
          (unambiguous-Trace M' true _)
          disjointParses
        )
        (⊕Aut≈ discAlpha M M' notBothNull disjointFirsts)

  -- caveat: this depends on the external `unambiguous-⊗` lemma
  -- from Grammar.SequentialUnambiguity.Properties
  --
  -- This should instead be refactored to build a retraction directly
  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notNullM : (M .null ≡ false))
    (seqUnambig :
      ∀ (c : ⟨ Alphabet ⟩) →
      (∀ (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    private
      ⊗A = ⊗Aut discAlpha M M' notNullM seqUnambig

      M⊛M' : Parse M ⊛ Parse M'
      M⊛M' c with seqUnambig c
      ... | Sum.inl h  = Sum.inl (¬FollowLastAut M c notNullM h)
      ... | Sum.inr eq = Sum.inr (¬FirstAut M' c eq)

      unambig-M⊗M' : unambiguous (Parse M ⊗ Parse M')
      unambig-M⊗M' =
        unambiguous-⊗
          (unambiguous-Trace M  true _)
          (unambiguous-Trace M' true _)
          M⊛M'

    ⊗Aut≅ : Parse ⊗A ≅ Parse M ⊗ Parse M'
    ⊗Aut≅ =
      ≈→≅
        (unambiguous-Trace ⊗A true _)
        unambig-M⊗M'
        (⊗Aut≈ discAlpha M M' notNullM seqUnambig)

  -- *Aut strong equivalence is not yet done
  -- It either needs an unambiguous-* external lemma akin to the ⊗ one
  -- or better yet, a retraction should be constructed directly
  -- *Aut≅ : Parse *Aut ≅ KL* (Parse M)
  -- *Aut≅ =
  --   ≈→≅
  --     (unambiguous-Trace *Aut true _)
  --     ?
  --     (*Aut≈ discAlpha M notNullM seqUnambig)
