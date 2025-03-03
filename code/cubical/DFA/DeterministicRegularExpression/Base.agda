{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module DFA.DeterministicRegularExpression.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.More
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Maybe as Maybe hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.SequentialUnambiguity Alphabet
-- open import DFA.Base Alphabet public
open import Automaton.Implicit Alphabet public
open import Term Alphabet

-- open DeterministicAutomaton

open ImplicitDeterministicAutomaton
open LogicalEquivalence

private
  variable
    ℓ ℓ' : Level

  -- mkFinSet : {Q : Type ℓ} → isFinSet Q → FinSet ℓ
  -- mkFinSet {Q = Q} _ .fst = FreelyAddFail+Initial Q
  -- mkFinSet isFinSetQ .snd =
  --   EquivPresIsFinSet
  --     (isoToEquiv (invIso (FreelyAddFail+Initial≅Unit⊎Unit⊎ _)))
  --     (isFinSet⊎
  --       (_ , isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSetUnit))
  --       (_ , isFinSetQ))

module _
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  ⊥Aut : ImplicitDeterministicAutomaton Empty.⊥
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δq ()
  ⊥Aut .δᵢ _ = fail

  ⊥≅ : Parse ⊥Aut ≅ ⊥
  ⊥≅ =
    ≈→≅
      (unambiguous-Trace ⊥Aut true _)
      unambiguous⊥
      (mkLogEq
        (rec _ ⊥Alg _)
        ⊥-elim
      )
    where
    ⊥Alg : ParseAlg ⊥Aut λ { initial → ⊥ }
    ⊥Alg fail = ParseAlgFail ⊥Aut _
    ⊥Alg initial =
      ⊕ᴰ-elim λ where
        (stepᵢ c) →
          ⊗⊥
          ∘g id ,⊗ ⊥*-elim
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  εAut : ImplicitDeterministicAutomaton Empty.⊥
  εAut .acc ()
  εAut .null = true
  εAut .δq ()
  εAut .δᵢ _ = fail

  ε≅ : Parse εAut ≅ ε
  ε≅ =
    ≈→≅
      (unambiguous-Trace εAut true _)
      unambiguousε
      (mkLogEq
        (rec _ εAlg _)
        (STOPᵢ εAut)
      )
    where
    εAlg : ParseAlg εAut λ { initial → ε }
    εAlg fail = ParseAlgFail εAut _
    εAlg initial =
      ⊕ᴰ-elim λ where
        stopᵢ → lowerG ∘g lowerG
        (stepᵢ c) →
          ⊥-elim
          ∘g ⊗⊥
          ∘g id ,⊗ ⊥*-elim
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  module _ (c : ⟨ Alphabet ⟩) where

    litAut : ImplicitDeterministicAutomaton Unit
    litAut .acc _ = true
    litAut .null = false
    -- litAut .δᵢ c' with DiscreteAlphabet isFinSetAlphabet c c'
    -- litAut .δᵢ c' | yes p = ↑f _
    -- litAut .δᵢ c' | no ¬p = fail
    litAut .δᵢ =
      discreteElim (DiscreteAlphabet isFinSetAlphabet) c
        (↑f _)
        λ _ → fail
    litAut .δq _ _ = fail

    lit≅ : Parse litAut ≅ ＂ c ＂
    lit≅ =
      ≈→≅
        (unambiguous-Trace litAut true _)
        (unambiguous-literal c)
        (mkLogEq
          (rec _ litAlg _)
          (toAut initial)
        )
      where
      ⟦_⟧lit : FreelyAddInitial Unit → Grammar ℓ-zero
      ⟦ initial ⟧lit = ＂ c ＂
      ⟦ ↑i _ ⟧lit = ε

      litAlg : ParseAlg litAut ⟦_⟧lit
      litAlg fail = ParseAlgFail litAut _
      litAlg initial =
        ⊕ᴰ-elim λ where
          (stepᵢ c') →
            initialStep c'
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        initialStep :
          (c' : ⟨ Alphabet ⟩) →
          ＂ c' ＂ ⊗ ParseAlgCarrier litAut ⟦_⟧lit (↑f→q (litAut .δᵢ c')) ⊢ ＂ c ＂
        initialStep c' with (DiscreteAlphabet isFinSetAlphabet c c')
        initialStep c' | yes p = J (λ c' c≡c' → ＂ c' ＂ ⊗ ε ⊢ ＂ c ＂) ⊗-unit-r p
        initialStep c' | no ¬p = ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim
      litAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q) → lowerG ∘g lowerG
          (step .q c) → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim ∘g (lowerG ∘g lowerG) ,⊗ lowerG

      toAut : ∀ q → ParseAlgCarrier litAut ⟦_⟧lit q ⊢ Trace litAut true q
      toAut fail = ⊥*-elim
      toAut initial =
        STEPᵢ litAut c
        ∘g id ,⊗ help
        ∘g id ,⊗ toAut (↑q _)
        ∘g ⊗-unit-r⁻
        where
        -- Weirdly need things like this to ensure that goals properly reduce
        help : Trace litAut true (↑q _) ⊢ Trace litAut true (↑f→q (litAut .δᵢ c))
        help with DiscreteAlphabet isFinSetAlphabet c c
        help | yes p = id
        help | no ¬p = Empty.rec (¬p refl)
      toAut (↑q _) = STOP litAut _

  module _
    {Q : Type ℓ}
    {Q' : Type ℓ'}
    (M : ImplicitDeterministicAutomaton Q)
    (M' : ImplicitDeterministicAutomaton Q')
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjointFirsts :
      ∀ (c : ⟨ Alphabet ⟩) →
      (fail ≡ M .δᵢ c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    ⊕Aut : ImplicitDeterministicAutomaton (Q ⊎ Q')
    ⊕Aut .acc (inl q) = M .acc q
    ⊕Aut .acc (inr q') = M' .acc q'
    ⊕Aut .null = M .null or M' .null
    ⊕Aut .δq (inl q) c with M .δq q c
    ⊕Aut .δq (inl q) c | fail = fail
    ⊕Aut .δq (inl q) c | ↑f qq = ↑f inl qq
    ⊕Aut .δq (inr q') c with M' .δq q' c
    ⊕Aut .δq (inr q') c | fail = fail
    ⊕Aut .δq (inr q') c | ↑f qq' = ↑f inr qq'
    ⊕Aut .δᵢ c with M .δᵢ c
    ⊕Aut .δᵢ c | fail with M' .δᵢ c
    ⊕Aut .δᵢ c | fail | fail = fail
    ⊕Aut .δᵢ c | fail | ↑f q' = ↑f inr q'
    ⊕Aut .δᵢ c | ↑f q = ↑f inl q

    private
      disjointParses : disjoint (Parse M) (Parse M')
      disjointParses =
        #→disjoint
          (λ c →
            {!Sum.map
              ?
              ?
              (disjointFirsts c)!}
          )
          {!!}

      ⟦_⟧M : FreelyAddInitial Q → Grammar ℓ
      ⟦ initial ⟧M = Parse M
      ⟦ ↑i q ⟧M = Trace M true (↑q q)

      ⟦_⟧M' : FreelyAddInitial Q' → Grammar ℓ'
      ⟦ initial ⟧M' = Parse M'
      ⟦ ↑i q' ⟧M' = Trace M' true (↑q q')

      ⟦_⟧⊕ : FreelyAddInitial (Q ⊎ Q') → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊕ = Parse M ⊕ Parse M'
      ⟦ ↑i (inl q) ⟧⊕ = LiftG ℓ' (Trace M true (↑q q))
      ⟦ ↑i (inr q') ⟧⊕ = LiftG ℓ (Trace M' true (↑q q'))


    ⊕Aut≅ : Parse ⊕Aut ≅ Parse M ⊕ Parse M'
    ⊕Aut≅ =
      ≈→≅
        (unambiguous-Trace ⊕Aut true _)
        (unambiguous⊕
          {!!}
          (unambiguous-Trace M true _)
          (unambiguous-Trace M' true _)
        )
        {!!}
