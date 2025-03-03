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
open import DFA.Base Alphabet public
open import Term Alphabet

open DeterministicAutomaton
open ImplicitDeterministicAutomaton
open LogicalEquivalence

private
  variable
    ℓ ℓ' : Level

  mkFinSet : {Q : Type ℓ} → isFinSet Q → FinSet ℓ
  mkFinSet {Q = Q} _ .fst = FreelyAddFail+Initial Q
  mkFinSet isFinSetQ .snd =
    EquivPresIsFinSet
      (isoToEquiv (invIso (FreelyAddFail+Initial≅Unit⊎Unit⊎ _)))
      (isFinSet⊎
        (_ , isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSetUnit))
        (_ , isFinSetQ))

module _
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  ⊥Aut : ImplicitDeterministicAutomaton Empty.⊥
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δq ()
  ⊥Aut .δᵢ _ = fail

  ⊥DFA : DFAOver (mkFinSet isFinSet⊥)
  ⊥DFA = Aut ⊥Aut

  ⊥DFA≅ : Parse ⊥DFA ≅ ⊥
  ⊥DFA≅ =
    ≈→≅
      (unambiguous-Trace ⊥DFA true _)
      unambiguous⊥
      (mkLogEq
        (rec _ ⊥Alg _)
        ⊥-elim
      )
    where
    ⊥Alg : AutAlg ⊥Aut ⊥ (λ ())
    ⊥Alg fail = AutAlg-fail ⊥Aut
    ⊥Alg initial =
      ⊕ᴰ-elim λ where
        step → ⊕ᴰ-elim (λ _ → ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG))

  εAut : ImplicitDeterministicAutomaton Empty.⊥
  εAut .acc ()
  εAut .null = true
  εAut .δq ()
  εAut .δᵢ _ = fail

  εDFA : DFAOver (mkFinSet isFinSet⊥)
  εDFA = Aut εAut

  εDFA≅ : Parse εDFA ≅ ε
  εDFA≅ =
    ≈→≅
      (unambiguous-Trace εDFA true _)
      unambiguousε
      (mkLogEq
        (rec _ εAlg _)
        (STOP εDFA)
      )
    where
    εAlg : AutAlg εAut ε (λ ())
    εAlg fail = AutAlg-fail εAut
    εAlg initial =
      ⊕ᴰ-elim λ where
        stop → ⊕ᴰ-elim λ _ → lowerG ∘g lowerG
        step → ⊕ᴰ-elim (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG))

  module _ (c : ⟨ Alphabet ⟩) where

    litAut : ImplicitDeterministicAutomaton Unit
    litAut .acc _ = true
    litAut .null = false
    litAut .δᵢ c' with DiscreteAlphabet isFinSetAlphabet c c'
    litAut .δᵢ c' | yes p = ↑f _
    litAut .δᵢ c' | no ¬p = fail
    -- litAut .δᵢ =
    --   discreteElim (DiscreteAlphabet isFinSetAlphabet) c
    --     (↑f _)
    --     λ _ → fail
      -- discreteElim (DiscreteAlphabet isFinSetAlphabet) c
      --   (↑f _)
      --   (λ _ → fail)
      --   c'
    litAut .δq _ _ = fail

    litDFA : DFAOver (mkFinSet isFinSetUnit)
    litDFA = Aut litAut

    litDFA≅ : Parse litDFA ≅ ＂ c ＂
    litDFA≅ =
      ≈→≅
        (unambiguous-Trace litDFA true _)
        (unambiguous-literal c)
        (mkLogEq
          (rec _ litAlg _)
          {!!}
          -- (toDFA initial)
        )
      where
      litAlg : AutAlg litAut ＂ c ＂ (λ _ → ε)
      litAlg fail = AutAlg-fail litAut
      litAlg initial =
        ⊕ᴰ-elim λ where
          step → ⊕ᴰ-elim λ where
            (lift c') →
              initialStep c'
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        initialStep :
          (c' : ⟨ Alphabet ⟩) →
          ＂ c' ＂ ⊗
            AutAlgCarrier litAut
              ＂ c ＂ (λ _ → ε) (litDFA .δ initial c') ⊢ ＂ c ＂
        initialStep c' with DiscreteAlphabet isFinSetAlphabet c c'
        initialStep c' | yes p =
          J (λ c'' c≡c'' → ＂ c'' ＂ ⊗ ε ⊢ ＂ c ＂) ⊗-unit-r p
        initialStep c' | no ¬p = ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim
      litAlg (↑q q) =
        ⊕ᴰ-elim λ where
          stop → ⊕ᴰ-elim (λ _ → lowerG ∘g lowerG)
          step → ⊕ᴰ-elim (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG))

      toDFA : ∀ q → AutAlgCarrier litAut ＂ c ＂ (λ _ → ε) q ⊢ Trace litDFA true q
      toDFA fail = ⊥*-elim
      toDFA initial =
        STEP litDFA {q = initial} c
        -- ∘g id ,⊗ {!id!}
        ∘g id ,⊗ transportG (cong (Trace litDFA true) {!!})
        ∘g id ,⊗ STOP litDFA {q = ↑q _}
        ∘g ⊗-unit-r⁻
      toDFA (↑q q) = STOP litDFA
