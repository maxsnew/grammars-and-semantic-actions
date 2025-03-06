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

  ⊥Aut : ImplicitDeterministicAutomaton ℓ-zero
  ⊥Aut .Q = Empty.⊥
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

  εAut : ImplicitDeterministicAutomaton ℓ-zero
  εAut .Q = Empty.⊥
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

    litAut : ImplicitDeterministicAutomaton ℓ-zero
    litAut .Q = Unit
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

      ⟦_⟧M : FreelyAddInitial (M .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse ⊕Aut
      ⟦ ↑i q ⟧M = Trace ⊕Aut true (↑q inl q)

      ⟦_⟧M' : FreelyAddInitial (M' .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' = Parse ⊕Aut
      ⟦ ↑i q' ⟧M' = Trace ⊕Aut true (↑q inr q')

      ⟦_⟧⊕ : FreelyAddInitial (⊕Aut .Q) → Grammar (ℓ-max ℓ ℓ')
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
        (stopᵢ x) →
          Sum.elim
            {C =
              λ y →
              true Eq.≡
                Sum.rec
                  (λ _ → M' .null)
                  (λ _ → M .null)
                  y
              → ε ⊢ Parse M ⊕ Parse M'}
            (λ _ → λ {Eq.refl → ⊕-inr ∘g STOPᵢ M'})
            (λ _ → λ {Eq.refl → ⊕-inl ∘g STOPᵢ M})
            notBothNull
            x
          ∘g lowerG ∘g lowerG
        (stepᵢ c) →
          Sum.elim
            {C = λ x →
              ＂ c ＂ ⊗
                ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                  (↑f→q
                    (Sum.rec
                      (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail inl (M .δᵢ c))
                      x
                    )
                  )
                ⊢ Parse M ⊕ Parse M'
            }
            (λ _ →
              ⊕-inr
              ∘g STEPᵢ M' c
              ∘g id ,⊗ helpL c
            )
            (λ _ →
              ⊕-inl
              ∘g STEPᵢ M c
              ∘g id ,⊗ helpR c
            )
            (disjointFirsts c)
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

          where
          helpL :
            (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                (↑f→q
                  (mapFreelyAddFail inr (M' .δᵢ c))
                )
              ⊢ Trace M' true (↑f→q (M' .δᵢ c))
          helpL c with M' .δᵢ c
          ... | fail = ⊥*-elim
          ... | ↑f q' = lowerG

          helpR :
            (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                (↑f→q
                  (mapFreelyAddFail inl (M .δᵢ c))
                )
              ⊢ Trace M true (↑f→q (M .δᵢ c))
          helpR c with M .δᵢ c
          ... | fail = ⊥*-elim
          ... | ↑f q = lowerG
    ⊕Alg (↑q (inl q)) =
      ⊕ᴰ-elim λ where
        (stop .(inl q) x) →
          liftG
          ∘g Eq.J (λ x y → ε ⊢ Trace M x (↑q q)) (STOP M q) (Eq.sym x)
          ∘g lowerG ∘g lowerG
        (step .(inl q) c) →
          liftG
          ∘g STEP M q c
          ∘g id ,⊗ help q c
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          where
          help :
            (q : M .Q) →
            (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                (↑f→q
                  (mapFreelyAddFail inl (M .δq q c))
                )
              ⊢ Trace M true (↑f→q (M .δq q c))
          help q c with M .δq q c
          ... | fail = ⊥*-elim
          ... | ↑f q = lowerG
    ⊕Alg (↑q (inr q')) =
      ⊕ᴰ-elim λ where
        (stop .(inr q') x) →
          liftG
          ∘g Eq.J (λ x y → ε ⊢ Trace M' x (↑q q')) (STOP M' q') (Eq.sym x)
          ∘g lowerG ∘g lowerG
        (step .(inr q') c) →
          liftG
          ∘g STEP M' q' c
          ∘g id ,⊗ help q' c
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          where
          help :
            (q' : (M' .Q)) →
            (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                (↑f→q
                  (mapFreelyAddFail inr (M' .δq q' c))
                )
              ⊢ Trace M' true (↑f→q (M' .δq q' c))
          help q' c with M' .δq q' c
          ... | fail = ⊥*-elim
          ... | ↑f q' = lowerG

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
    ⊗Aut .acc (inl q) = M' .null
    ⊗Aut .acc (inr q') = M' .acc q'
    ⊗Aut .null = false
    ⊗Aut .δq (inl q) c =
      if (M .acc q)
      then
        (Sum.rec
          (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
          (λ x → mapFreelyAddFail inl (M .δq q c))
          (seqUnambig c))
      else mapFreelyAddFail inl (M .δq q c)
    ⊗Aut .δq (inr q') c = mapFreelyAddFail inr (M' .δq q' c)
    ⊗Aut .δᵢ c = mapFreelyAddFail inl (M .δᵢ c)

    private
      M⊛M' : Parse M ⊛ Parse M'
      M⊛M' = {!!}

      ⟦_⟧M : FreelyAddInitial (M .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse ⊗Aut
      ⟦ ↑i q ⟧M =
        &[ c ∈ ⟨ Alphabet ⟩ ]
        &[ _ ∈ M .acc q ≡ true ]
        &[ _ ∈ fail ≡ M .δq q c ]
          ((＂ c ＂ ⊗ Trace ⊗Aut true (↑f→q (mapFreelyAddFail inr (M' .δᵢ c)))) ⊸ Trace ⊗Aut true (↑q inl q))

      ⟦_⟧M' : FreelyAddInitial (M' .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' =
        &[ q ∈ M .Q ]
        &[ _ ∈ M .acc q ≡ true ]
          Trace ⊗Aut true (↑q inl q)

        -- &[ c ∈ ⟨ Alphabet ⟩ ]
        -- &[ q ∈ M .Q ]
        -- &[ _ ∈ M .acc q ≡ true ]
        -- &[ _ ∈ fail ≡ M .δq q c ]
        -- &[ (c , q , _ , _) ∈
        --   Σ[ c ∈ ⟨ Alphabet ⟩ ]
        --   Σ[ q ∈ M .Q ]
        --   Σ[ _ ∈ M .acc q ≡ true ]
        --     fail ≡ M .δq q c ]
        --   (startsWith c & Trace ⊗Aut true (↑q inl q))
      ⟦ ↑i q' ⟧M' = Trace ⊗Aut true (↑q inr q')

      ⟦_⟧⊗ : FreelyAddInitial (⊗Aut .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊗ = Parse M ⊗ Parse M'
      ⟦ ↑i (inl q) ⟧⊗ = Trace ⊗Aut true (↑q inl q) ⊗ Parse M'
      ⟦ ↑i (inr q') ⟧⊗ = Trace ⊗Aut true (↑q inr q')

      M'Alg : ParseAlg M' ⟦_⟧M'
      M'Alg fail = ParseAlgFail M' _
      M'Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            &ᴰ-in (λ q →
              &ᴰ-in (λ acc →
                STOP ⊗Aut (inl q)
              )
            )
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            &ᴰ-in (λ q →
              &ᴰ-in (λ acc →
                STEP ⊗Aut (inl q) c
                ∘g id ,⊗ help c q acc
              )
            )
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        help :
          (c : ⟨ Alphabet ⟩) →
          (q : M .Q) →
          M .acc q ≡ true →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c)) ⊢ Trace ⊗Aut true _
        -- help c q isAcc =
        --   -- {!J
        --   --   (λ x y → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c)) )!}
        --   Sum.elim
        --     {C = λ x →
        --        ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c)) ⊢
        --        Trace ⊗Aut true
        --          (↑f→q
        --            (if M .acc q then
        --               Sum.rec
        --                 (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
        --                 (λ _ → mapFreelyAddFail inl (M .δq q c))
        --                 x
        --             else
        --             mapFreelyAddFail inl (M .δq q c))
        --          )
        --     }
        --     (λ f → {!!})
        --     {!!}
        --     (seqUnambig c)

        help c q acc with M' .δᵢ c
        help c q acc | fail = ⊥*-elim
        help c q acc | ↑f q' =
          ?
      -- -- -- (↑f→q
      -- -- --  (if Automaton.Implicit.ImplicitDeterministicAutomaton.acc M q then
      -- -- --   Sum.rec
      -- -- --   (λ _ →
      -- -- --      mapFreelyAddFail inr
      -- -- --      (Automaton.Implicit.ImplicitDeterministicAutomaton.δᵢ M' c))
      -- -- --   (λ x →
      -- -- --      mapFreelyAddFail inl
      -- -- --      (Automaton.Implicit.ImplicitDeterministicAutomaton.δq M q c))
      -- -- --   (seqUnambig c)
      -- -- --   else
      -- -- --   mapFreelyAddFail inl
      -- -- --   (Automaton.Implicit.ImplicitDeterministicAutomaton.δq M q c)))
      --     J
      --       (λ x y →
      --         Trace ⊗Aut true (↑q inr q') ⊢
      --         Trace ⊗Aut true
      --           (↑f→q
      --             (if x
      --             then Sum.rec
      --               (λ _ → mapFreelyAddFail inr (M' .δᵢ c))
      --               (λ _ → mapFreelyAddFail inl (M .δq q c))
      --               (seqUnambig c)
      --             else mapFreelyAddFail inl (M .δq q c))
      --           )
      --           )
      --           (Sum.elim
      --             {C = λ x →
      --               Trace ⊗Aut true (↑q inr q') ⊢
      --               Trace ⊗Aut true
      --                 (↑f→q
      --                 (Sum.rec
      --                   _
      --                   _
      --                   x)
      --                 )
      --             }
      --             (λ f → {!!})
      --             (λ notAcc' → {!!})
      --             (seqUnambig c))
      --           (sym acc)
      --   -- help c q acc | ↑f q' | true = ?
      --   -- stepInitial : (c : ⟨ Alphabet ⟩) →
      --   --   ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
      --   --     ⊢ ParseAlgCarrier M' ⟦_⟧M' initial
      --   -- stepInitial c with M' .δᵢ c
      --   -- ... | fail = ⊗⊥*-elim
      --   -- ... | ↑f q' =
      --   --   &ᴰ-in (λ q →
      --   --     &ᴰ-in (λ acc →
      --   --       J (λ x y → ＂ c ＂ ⊗ Trace ⊗Aut x (↑q inr q') ⊢ Trace ⊗Aut true (↑q inl q))
      --   --         (STEP ⊗Aut (inl q) c ∘g id ,⊗ {!!}) acc
      --   --         -- ({!!} ∘g STEP ⊗Aut {!inr q'!} c)
      --   --     )
      --   --   )

      M'Alg (↑q q') =
        ⊕ᴰ-elim λ where
          (stop .q' x) → {!!}
          (step .q' c) → {!!}

      MAlg : ParseAlg M ⟦_⟧M
      MAlg fail = ParseAlgFail M _
      MAlg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) → Empty.rec (true≢false notNullM)
          (stepᵢ c) → {!!}
      MAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q x) → {!!}
          (step .q c) → {!!}
