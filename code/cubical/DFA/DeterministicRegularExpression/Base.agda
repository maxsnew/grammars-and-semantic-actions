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
          ⊗⊥*-elim
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
        (stopᵢ Eq.refl) → lowerG ∘g lowerG
        (stepᵢ c) →
          ⊗⊥*-elim
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  module _ (c : ⟨ Alphabet ⟩) where

    litAut : ImplicitDeterministicAutomaton Unit
    litAut .acc _ = true
    litAut .null = false
    litAut .δᵢ c' =
      decRec
        (λ _ → ↑f _)
        (λ _ → fail)
        (DiscreteAlphabet isFinSetAlphabet c c')
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
        initialStep c' =
          decElim
            {A = λ x →
              ＂ c' ＂ ⊗
                  ParseAlgCarrier litAut ⟦_⟧lit
                    (↑f→q
                      (decRec
                        (λ _ → ↑f _)
                        (λ _ → fail)
                        x
                      )
                    )
                  ⊢ ＂ c ＂
            }
            (J (λ c'' c≡c'' → ＂ c'' ＂ ⊗ ε ⊢ ＂ c ＂) ⊗-unit-r)
            (λ _ → ⊗⊥*-elim)
            (DiscreteAlphabet isFinSetAlphabet c c')

      litAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q Eq.refl) → lowerG ∘g lowerG
          (step .q c) → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim ∘g (lowerG ∘g lowerG) ,⊗ lowerG

      toAut : ∀ q → ParseAlgCarrier litAut ⟦_⟧lit q ⊢ Trace litAut true q
      toAut fail = ⊥*-elim
      toAut initial =
        STEPᵢ litAut c
        ∘g id ,⊗
          decElim
            {A =
              λ x →
              Trace litAut true (↑q _)
              ⊢
              Trace litAut true
                (↑f→q (decRec (λ _ → ↑f _) (λ _ → fail) x))
            }
            (λ _ → id)
            (λ ¬p → Empty.rec (¬p refl))
            (DiscreteAlphabet isFinSetAlphabet c c)
        ∘g id ,⊗ toAut (↑q _)
        ∘g ⊗-unit-r⁻
      toAut (↑q _) = STOP litAut _

  module _
    {Q : Type ℓ}
    {Q' : Type ℓ'}
    -- TODO Q not param
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
    ⊕Aut .null =
      Sum.rec
        (λ _ → M' .null)
        (λ _ → M .null)
        notBothNull
    ⊕Aut .δq (inl q) c = mapFreelyAddFail inl (M .δq q c)
    ⊕Aut .δq (inr q') c = mapFreelyAddFail inr (M' .δq q' c)
    ⊕Aut .δᵢ c =
      Sum.rec
        (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
        (λ _ → mapFreelyAddFail inl (M .δᵢ c))
        (disjointFirsts c)

    private
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

      ⟦_⟧M : FreelyAddInitial Q → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse ⊕Aut
      ⟦ ↑i q ⟧M = Trace ⊕Aut true (↑q inl q)

      ⟦_⟧M' : FreelyAddInitial Q' → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' = Parse ⊕Aut
      ⟦ ↑i q' ⟧M' = Trace ⊕Aut true (↑q inr q')

      ⟦_⟧⊕ : FreelyAddInitial (Q ⊎ Q') → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊕ = Parse M ⊕ Parse M'
      ⟦ ↑i (inl q) ⟧⊕ = LiftG ℓ' (Trace M true (↑q q))
      ⟦ ↑i (inr q') ⟧⊕ = LiftG ℓ (Trace M' true (↑q q'))

      MAlg : ParseAlg M ⟦_⟧M
      MAlg fail = ParseAlgFail M _
      MAlg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            Sum.elim
              {C = λ x →
                Trace ⊕Aut
                  (Sum.rec
                    (λ _ → M' .null)
                    (λ _ → M .null)
                    x)
                  initial ⊢
                  Parse ⊕Aut}
              (λ x → Empty.rec (true≢false x))
              (λ _ → id)
              notBothNull
            ∘g STOPᵢ ⊕Aut
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            stepInitial c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitial : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
            ⊢ ParseAlgCarrier M ⟦_⟧M initial
        stepInitial c =
          STEPᵢ ⊕Aut c
          ∘g id ,⊗
            Sum.elim
              {C = λ x →
                ParseAlgCarrier M ⟦_⟧M
                  (↑f→q (M .δᵢ c))
                ⊢
                Trace ⊕Aut true
                  (↑f→q
                    (Sum.rec
                      (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail inl (M .δᵢ c))
                      x
                    )
                  )
              }
              (J
                (λ x y →
                  ParseAlgCarrier M ⟦_⟧M (↑f→q x)
                  ⊢
                  Trace ⊕Aut true (↑f→q (mapFreelyAddFail inr (M' .δᵢ c)))
                )
                ⊥*-elim)
              (λ _ → help)
              (disjointFirsts c)
            where
            help :
              ParseAlgCarrier M ⟦_⟧M
                (↑f→q (M .δᵢ c))
              ⊢
              Trace ⊕Aut true
               (↑f→q
                (mapFreelyAddFail inl
                 (M .δᵢ c)))
            help with M .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f x = id
      MAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q x) →
            Eq.J (λ b tEq≡b → ε ⊢ Trace ⊕Aut b (↑q inl q)) (STOP ⊕Aut (inl q)) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .q c) →
            STEP ⊕Aut (inl q) c
            ∘g id ,⊗ help c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help : (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier M ⟦_⟧M
                (↑f→q
                  (M .δq q c)
                )
              ⊢
              Trace ⊕Aut true
                (↑f→q
                  (mapFreelyAddFail inl (M .δq q c))
                )
            help c with M .δq q c
            ... | fail = ⊥*-elim
            ... | ↑f x = id

      M'Alg : ParseAlg M' ⟦_⟧M'
      M'Alg fail = ParseAlgFail M' _
      M'Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            Sum.elim
              {C = λ x →
                Trace ⊕Aut
                  (Sum.rec
                    (λ _ → M' .null)
                    (λ _ → M .null)
                    x)
                  initial ⊢
                  Parse ⊕Aut}
              (λ _ → id)
              (λ x → Empty.rec (true≢false x))
              notBothNull
            ∘g STOPᵢ ⊕Aut
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            stepInitial c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitial : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
            ⊢ ParseAlgCarrier M' ⟦_⟧M' initial
        stepInitial c =
          STEPᵢ ⊕Aut c
          ∘g id ,⊗
            Sum.elim
              {C = λ x →
                ParseAlgCarrier M' ⟦_⟧M'
                  (↑f→q (M' .δᵢ c))
                ⊢
                Trace ⊕Aut true
                  (↑f→q
                    (Sum.rec
                      (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail inl (M .δᵢ c))
                      x
                    )
                  )
              }
              (λ _ → help)
              (J
                (λ x y →
                  ParseAlgCarrier M' ⟦_⟧M' (↑f→q x)
                  ⊢
                  Trace ⊕Aut true (↑f→q (mapFreelyAddFail inl (M .δᵢ c)))
                )
                ⊥*-elim)
              (disjointFirsts c)
            where
            help :
              ParseAlgCarrier M' ⟦_⟧M'
                (↑f→q (M' .δᵢ c))
              ⊢
              Trace ⊕Aut true
               (↑f→q
                (mapFreelyAddFail inr
                 (M' .δᵢ c)))
            help with M' .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f x = id
      M'Alg (↑q q') =
        ⊕ᴰ-elim λ where
          (stop .q' x) →
            Eq.J (λ b tEq≡b → ε ⊢ Trace ⊕Aut b (↑q inr q')) (STOP ⊕Aut (inr q')) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .q' c) →
            STEP ⊕Aut (inr q') c
            ∘g id ,⊗ help c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help : (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier M' ⟦_⟧M'
                (↑f→q
                  (M' .δq q' c)
                )
              ⊢
              Trace ⊕Aut true
                (↑f→q
                  (mapFreelyAddFail inr (M' .δq q' c))
                )
            help c with M' .δq q' c
            ... | fail = ⊥*-elim
            ... | ↑f x = id

    ⊕Alg : ParseAlg ⊕Aut ⟦_⟧⊕
    ⊕Alg fail = ParseAlgFail ⊕Aut _
    ⊕Alg initial =
      ⊕ᴰ-elim λ where
        (stopᵢ x) → {!!}
        (stepᵢ c) → {!!}
    ⊕Alg (↑q (inl q)) =
      ⊕ᴰ-elim λ where
        (stop .(inl q) x) → {!!}
        (step .(inl q) c) → {!!}
    ⊕Alg (↑q (inr q')) =
      ⊕ᴰ-elim λ where
        (stop .(inr q') x) → {!!}
        (step .(inr q') c) → {!!}

    M→⊕Aut : Parse M ⊢ Parse ⊕Aut
    M→⊕Aut = rec _ MAlg initial

    M'→⊕Aut : Parse M' ⊢ Parse ⊕Aut
    M'→⊕Aut = rec _ M'Alg initial

    ⊕Aut≅ : Parse ⊕Aut ≅ Parse M ⊕ Parse M'
    ⊕Aut≅ =
      ≈→≅
        (unambiguous-Trace ⊕Aut true _)
        (unambiguous⊕
          disjointParses
          (unambiguous-Trace M true _)
          (unambiguous-Trace M' true _)
        )
        (mkLogEq
          (rec _ ⊕Alg initial)
          (⊕-elim M→⊕Aut M'→⊕Aut)
        )
