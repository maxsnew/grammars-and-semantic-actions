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
open import Cubical.Data.Bool.More
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Maybe.More
open import Cubical.Data.Maybe.PartialFunction

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

private
  variable
    ℓ ℓ' : Level

  mkFinSet : {A : Type ℓ} → isFinSet A → FinSet ℓ
  mkFinSet {A = A} _ .fst = Maybe (FreeInitial A)
  mkFinSet isFinSetA .snd =
    isFinSetMaybe
      (EquivPresIsFinSet
        (isoToEquiv (invIso (FreeInitial≅Unit⊎ _)))
        (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSetA)))

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
    ⊥Alg : AutAlg ⊥Aut (λ _ → ⊥)
    ⊥Alg nothing = ⊥-elim ∘g AutAlg-nothing ⊥Aut
    ⊥Alg (just initial) =
      ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim λ { ()}
      ; step → ⊕ᴰ-elim (λ _ → ⊗⊥ ∘g id ,⊗ (lowerG ∘g lowerG))
      })

  εAut : ImplicitDeterministicAutomaton Empty.⊥
  εAut .acc ()
  εAut .null = true
  εAut .δ₀ _ _ = nothing

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
    εAlg : AutAlg εAut (λ _ → ε)
    εAlg nothing = ⊥-elim ∘g AutAlg-nothing εAut
    εAlg (just initial) =
      ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim λ _ → lowerG ∘g lowerG
      ; step → ⊕ᴰ-elim (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ (lowerG ∘g lowerG))
      })

  module _ (c : ⟨ Alphabet ⟩) where
    private
      module _ (c' : ⟨ Alphabet ⟩) where
        open ElimDecRec
          (DecProp≡ (DiscreteAlphabet isFinSetAlphabet) c c')
          (Maybe Unit)
          (λ _ → just _)
          (λ _ → nothing)
          -- (λ _ → λ { (inl _) → just _ ; (inr _) → nothing })
          -- (λ _ _ → nothing)

        mkδ₀ : Maybe Unit
        mkδ₀ = the-dec-rec

        module _
          {C : Maybe Unit → Type ℓ}
          where
          elim-≡ : c ≡ c' → C (just _) → C mkδ₀
          elim-≡ = decRecYes {C = C}

          elim-≢ : ¬ (c ≡ c') → C nothing → C mkδ₀
          elim-≢ = decRecNo {C = C}

          c≡c'? = decRecMap {C = C}

    litAut : ImplicitDeterministicAutomaton Unit
    litAut .acc _ = true
    litAut .null = false
    litAut .δ₀ initial c' = mkδ₀ c'
    litAut .δ₀ (↑ _) _ = nothing

    litDFA : DFAOver (mkFinSet isFinSetUnit)
    litDFA = Aut litAut

    litDFA≅ : Parse litDFA ≅ ＂ c ＂
    litDFA≅ =
      ≈→≅
        (unambiguous-Trace litDFA true _)
        (unambiguous-literal c)
        (mkLogEq
          (rec _ litAlg _)
          (toDFA initial)
        )
      where
      ⟦_⟧st : FreeInitial Unit → Grammar ℓ-zero
      ⟦ initial ⟧st = ＂ c ＂
      ⟦ ↑ _ ⟧st = ε

      litAlg : AutAlg litAut ⟦_⟧st
      litAlg nothing = ⊥-elim ∘g AutAlg-nothing litAut
      litAlg (just initial) =
        ⊕ᴰ-elim (λ {
          stop → ⊕ᴰ-elim λ {()}
        ; step →
          ⊕ᴰ-elim λ {
            c' →
              c≡c'? c'
                {C = λ x →
                  ＂ c' ＂ ⊗ implicitFailCarrier litAut ⟦_⟧st (map-Maybe ↑_ x) ⊢ ＂ c ＂
                }
                (λ c≡c' → transportG (cong ＂_＂ (sym c≡c')) ∘g ⊗-unit-r)
                (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ lowerG)
              ∘g lowerG ,⊗ lowerG
            }
        })
      litAlg (just (↑ _)) =
        ⊕ᴰ-elim (λ {
          stop → ⊕ᴰ-elim λ _ → lowerG ∘g lowerG
        ; step → ⊕ᴰ-elim (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ (lowerG ∘g lowerG))
        })

      toDFA : ∀ q → ⟦ q ⟧st ⊢ Trace litDFA true (just q)
      toDFA initial =
        STEP litDFA {q = just initial} c
        ∘g id ,⊗
          transportG
            (cong (λ z → Trace litDFA true z)
              (elim-≡ c {C = λ x → just (↑ _) ≡ map-Maybe ↑_ x} refl refl)
            )
        ∘g id ,⊗ STOP litDFA {q = just (↑ _)}
        ∘g ⊗-unit-r⁻
      toDFA (↑ _) = STOP litDFA

  module _
    {Q : FinSet ℓ}
    {Q' : FinSet ℓ'}
    (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
    (M' : ImplicitDeterministicAutomaton ⟨ Q' ⟩)
    (notBothNull : (M .null Eq.≡ false) ⊎ (M' .null Eq.≡ false))
    (disjoint-firsts : disjointDomains (M .δ₀ initial) (M' .δ₀ initial))
    where
    private
      MDFA = Aut M
      M'DFA = Aut M'

      Q⊕ : FinSet (ℓ-max ℓ ℓ')
      Q⊕ .fst = ⟨ Q ⟩ ⊎ ⟨ Q' ⟩
      Q⊕ .snd = isFinSet⊎ Q Q'

      disjointParses : disjoint (Parse MDFA) (Parse M'DFA)
      disjointParses =
        #→disjoint
          (λ c →
            Sum.map
              (¬FirstAut M c)
              (¬FirstAut M' c)
              (disjoint-firsts c)
          )
          (Sum.map
            (¬NullAut M ∘ Eq.eqToPath)
            (¬NullAut M' ∘ Eq.eqToPath)
            notBothNull
            )

    ⊕Aut : ImplicitDeterministicAutomaton (⟨ Q ⟩ ⊎ ⟨ Q' ⟩)
    ⊕Aut .acc (inl q) = M .acc q
    ⊕Aut .acc (inr q') = M' .acc q'
    ⊕Aut .null = M .null or M' .null
    ⊕Aut .δ₀ initial =
      union⊎
        (M .δ₀ initial) (M' .δ₀ initial)
        disjoint-firsts
    ⊕Aut .δ₀ (↑ (inl q)) c = map-Maybe inl (M .δ₀ (↑ q) c)
    ⊕Aut .δ₀ (↑ (inr q')) c = map-Maybe inr (M' .δ₀ (↑ q') c)

    ⊕DFA : DFAOver (mkFinSet (isFinSet⊎ Q Q'))
    ⊕DFA = Aut ⊕Aut

    ⊕DFA≅ : Parse ⊕DFA ≅ Parse MDFA ⊕ Parse M'DFA
    ⊕DFA≅ =
      ≈→≅
        (unambiguous-Trace ⊕DFA true _)
        (unambiguous⊕
          disjointParses
          (unambiguous-Trace MDFA true _)
          (unambiguous-Trace M'DFA true _)
        )
        (mkLogEq
          {!!}
          {!!}
        )
      where
      -- ⟦_⟧⊕ : ⟨ mkFinSet (Q⊕ .snd) ⟩ → Bool → Grammar (ℓ-max ℓ ℓ')
      -- ⟦ nothing ⟧⊕ b = ⊤*
      -- ⟦ just initial ⟧⊕ b = Trace MDFA b (just initial) ⊕ Trace M'DFA b (just initial)
      -- ⟦ just (↑ inl q) ⟧⊕ b = LiftG ℓ' (Trace MDFA b (just (↑ q)))
      -- ⟦ just (↑ inr q') ⟧⊕ b = LiftG ℓ (Trace M'DFA b (just (↑ q')))

      -- ⊕Alg : {!TraceAlg ⊕DFA !}
      -- ⊕Alg = {!!}

      ⟦_⟧⊕ : FreeInitial (⟨ Q ⟩ ⊎ ⟨ Q' ⟩) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊕ = Parse MDFA ⊕ Parse M'DFA
      ⟦ ↑ (inl q) ⟧⊕ = LiftG ℓ' (Trace MDFA true (just (↑ q)))
      ⟦ ↑ (inr q') ⟧⊕ = LiftG ℓ (Trace M'DFA true (just (↑ q')))

      ⟦_⟧M : FreeInitial ⟨ Q ⟩ → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse ⊕DFA
      ⟦ ↑ q ⟧M = Trace ⊕DFA true (just (↑ inl q))

      ⟦_⟧M' : FreeInitial ⟨ Q' ⟩ → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' = Parse ⊕DFA
      ⟦ ↑ q' ⟧M' = Trace ⊕DFA true (just (↑ inr q'))

      initialStep : (c : ⟨ Alphabet ⟩) →
        ＂ c ＂ ⊗ _ ⊢ Parse MDFA ⊕ Parse M'DFA
      initialStep c with union⊎ (M .δ₀ initial) (M' .δ₀ initial) disjoint-firsts c in eq
      initialStep c | nothing =
        ⊥-elim
        ∘g ⊗⊥
        ∘g id ,⊗
            (lowerG
            ∘g transportG
              (cong (λ z → implicitFailCarrier ⊕Aut ⟦_⟧⊕ (map-Maybe ↑_ z))
              (Eq.eqToPath eq)))
      initialStep c | just (inl q) with
        {!isEmbedding→Inj
          isEmbedding-just
          q

          !}
        in eq'
        -- with mkFiber-f _ _ disjoint-firsts c
        --   (q , (sym (Eq.eqToPath eq))) in eq'
      initialStep c | just (inl q) | x =
        ⊕-inl
        ∘g STEP (Aut M) c
        ∘g id ,⊗ {!x!}
        -- ∘g id ,⊗
        --     (transportG
        --       (cong (λ z → Trace MDFA true (map-Maybe ↑_ z))
        --       {!!}))
        ∘g id ,⊗
            (lowerG
            ∘g transportG
              (cong (λ z → implicitFailCarrier ⊕Aut ⟦_⟧⊕ (map-Maybe ↑_ z))
              (Eq.eqToPath eq)))
      initialStep c | just (inr q') =
        {!!}
        ∘g {!!}

  --     ⊕Alg : AutAlg ⊕Aut ⟦_⟧⊕
  --     ⊕Alg nothing = ⊥-elim ∘g AutAlg-nothing ⊕Aut
  --     ⊕Alg (just initial) =
  --       ⊕ᴰ-elim λ {
  --           stop →
  --             Sum.rec
  --               (λ {Eq.refl →
  --                 ⊕ᴰ-elim λ {
  --                   Eq.refl →
  --                     ⊕-inr
  --                     ∘g STOP M'DFA
  --                     ∘g lowerG ∘g lowerG
  --                 }
  --               })
  --               (λ {Eq.refl →
  --                 ⊕ᴰ-elim λ {x →
  --                   ⊕-inl
  --                   ∘g
  --                     Eq.transport
  --                       (λ b → ε ⊢ Trace MDFA b (just initial))
  --                       (Eq.sym (x Eq.∙ or-false))
  --                       (STOP MDFA {q = just initial})
  --                   ∘g lowerG ∘g lowerG
  --                 }
  --               })
  --               notBothNull
  --         ; step → ⊕ᴰ-elim (λ c →
  --           initialStep c
  --           -- Sum.rec
  --           --   (λ {
  --           --     (inl q , x) →
  --           --       ⊕-inl
  --           --       ∘g STEP MDFA c
  --           --       ∘g id ,⊗ transportG (cong (Trace MDFA true)
  --           --                  {!union⊎-map-fiber ? ? ? ?
  --           --                  (map-Maybe-fiber {f = ↑_} _ (_ , sym x)) !}
  --           --                  )
  --           --       ∘g id ,⊗ lowerG
  --           --       ∘g id ,⊗ transportG (cong (implicitFailCarrier ⊕Aut ⟦_⟧⊕) x)
  --           --   ; (inr q' , x) → {!!}
  --           --   })
  --           --   (λ x →
  --           --     ⊥-elim
  --           --     ∘g ⊗⊥
  --           --     ∘g id ,⊗ lowerG
  --           --     ∘g id ,⊗ transportG (cong (implicitFailCarrier ⊕Aut ⟦_⟧⊕) x)
  --           --   )
  --           --   (noMapsIntoInit ⊕Aut (just initial) c)
  --           ∘g lowerG ,⊗ lowerG
  --         )
  --       }
  --     ⊕Alg (just (↑ (inl q))) =
  --       ⊕ᴰ-elim λ {
  --           stop → ⊕ᴰ-elim (λ {acc →
  --             liftG
  --             ∘g Eq.transport (λ b → ε ⊢ Trace MDFA b (just (↑ q)))
  --                   (Eq.sym acc)
  --                   (STOP MDFA)
  --             ∘g lowerG ∘g lowerG
  --           })
  --         ; step → ⊕ᴰ-elim (λ c →
  --           liftG
  --           ∘g {!!}
  --           ∘g lowerG ,⊗ lowerG
  --         )
  --       }
  --     ⊕Alg (just (↑ (inr q'))) = {!!}
  --       -- ⊕ᴰ-elim λ {
  --       --     stop → ?
  --       --   ; step → ?
  --       -- }

  --     MAlg : AutAlg M ⟦_⟧M
  --     MAlg nothing = ⊥-elim ∘g AutAlg-nothing M
  --     MAlg (just initial) =
  --       ⊕ᴰ-elim λ {
  --           stop → ⊕ᴰ-elim λ {
  --             Eq.refl →
  --               STOP ⊕DFA
  --               ∘g lowerG ∘g lowerG
  --           }
  --         ; step → ⊕ᴰ-elim λ {
  --             c →
  --               {!!}
  --               ∘g lowerG ,⊗ lowerG
  --           }
  --       }
  --     MAlg (just (↑ q)) =
  --       ⊕ᴰ-elim λ {
  --           stop → {!!}
  --         ; step → {!!}
  --       }

  -- --     M'Alg : AutAlg M' ⟦_⟧M'
  -- --     M'Alg nothing = ⊥-elim ∘g AutAlg-nothing M'
  -- --     M'Alg (just initial) = {!!}
  -- --     M'Alg (just (↑ q)) = {!!}

  -- --     -- toDFA : ∀ q → ⟦ q ⟧st ⊢ Trace litDFA true (just q)
  -- --     -- toDFA initial =
  -- --     --   STEP litDFA {q = just initial} c
  -- --     --   ∘g id ,⊗
  -- --     --     transportG
  -- --     --       (cong (λ z → Trace litDFA true z)
  -- --     --         (elim-≡ c {C = λ x → just (↑ _) ≡ map-Maybe ↑_ x} refl refl)
  -- --     --       )
  -- --     --   ∘g id ,⊗ STOP litDFA {q = just (↑ _)}
  -- --     --   ∘g ⊗-unit-r⁻
  -- --     -- toDFA (↑ _) = STOP litDFA



  -- -- module _
  -- --   {Q : FinSet ℓ}
  -- --   {Q' : FinSet ℓ'}
  -- --   (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
  -- --   (M' : ImplicitDeterministicAutomaton ⟨ Q' ⟩)
  -- --   (notNullM : M .null ≡ false)
  -- --   (seq-unambig :
  -- --     ∀ (q : ⟨ Q ⟩) →
  -- --     M .acc q ≡ true →
  -- --     disjointDomains (M .δ₀ (↑ q)) (M' .δ₀ initial))
  -- --   where

  -- --   ⊗Aut : ImplicitDeterministicAutomaton (⟨ Q ⟩ ⊎ ⟨ Q' ⟩)
  -- --   ⊗Aut .acc (inl q) = if M' .null then M .acc q else false
  -- --   ⊗Aut .acc (inr q') = M' .acc q'
  -- --   ⊗Aut .null = false
  -- --   ⊗Aut .δ₀ initial c = map-Maybe inl (M .δ₀ initial c)
  -- --   ⊗Aut .δ₀ (↑ (inl q)) =
  -- --     if' M .acc q then
  -- --       (λ qIsAcc → union⊎ (M .δ₀ (↑ q)) (M' .δ₀ initial) (seq-unambig q qIsAcc))
  -- --       else
  -- --       (λ _ →
  -- --         (λ c → map-Maybe inl (M .δ₀ (↑ q) c))
  -- --       )
  -- --   ⊗Aut .δ₀ (↑ (inr q')) c = map-Maybe inr (M' .δ₀ (↑ q') c)

  -- --   ⊗DFA : DFAOver (mkFinSet (isFinSet⊎ Q Q'))
  -- --   ⊗DFA = Aut ⊗Aut

  -- -- module _
  -- --   {Q : FinSet ℓ}
  -- --   (M : ImplicitDeterministicAutomaton ⟨ Q ⟩)
  -- --   (notNullM : M .null ≡ false)
  -- --   (seq-unambig :
  -- --     ∀ (q : ⟨ Q ⟩) →
  -- --     M .acc q ≡ true →
  -- --     disjointDomains (M .δ₀ (↑ q)) (M .δ₀ initial))
  -- --   where

  -- --   *Aut : ImplicitDeterministicAutomaton ⟨ Q ⟩
  -- --   *Aut .acc = M .acc
  -- --   *Aut .null = true
  -- --   *Aut .δ₀ initial = M .δ₀ initial
  -- --   *Aut .δ₀ (↑ q) =
  -- --     if' M .acc q then
  -- --       (λ qIsAcc → union (M .δ₀ (↑ q)) (M .δ₀ initial) (seq-unambig q qIsAcc))
  -- --       else
  -- --       (λ _ → M .δ₀ (↑ q))

  -- --   *DFA : DFAOver (mkFinSet (Q .snd))
  -- --   *DFA = Aut *Aut
