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
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
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
    ⊥Alg (just (inl tt)) =
      ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim λ { (lift ())}
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
    εAlg (just (inl tt)) =
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
    litAut .δ₀ (inl _) c' = mkδ₀ c'
    litAut .δ₀ (inr _) _ = nothing
    -- litAut .δ₀ (inl _) c' =
      -- decRec
      --   (λ _ → just _)
      --   (λ _ → nothing)
      --   (DiscreteAlphabet isFinSetAlphabet c c')
    -- litAut .δ₀ (inr q) _ = nothing

    litDFA : DFAOver (mkFinSet isFinSetUnit)
    litDFA = Aut litAut

    litDFA≅ : Parse litDFA ≅ ＂ c ＂
    litDFA≅ =
      ≈→≅
        (unambiguous-Trace litDFA true _)
        (unambiguous-literal c)
        (mkLogEq
          (rec _ litAlg _)
          (toDFA (inl tt))
        )
      where
      ⟦_⟧st : Unit ⊎ Unit → Grammar ℓ-zero
      ⟦ inl _ ⟧st = ＂ c ＂
      ⟦ inr _ ⟧st = ε

      litAlg : AutAlg litAut ⟦_⟧st
      litAlg nothing = ⊥-elim ∘g AutAlg-nothing litAut
      litAlg (just (inl _)) =
        ⊕ᴰ-elim (λ {
          stop → ⊕ᴰ-elim λ {()}
        ; step →
          ⊕ᴰ-elim λ {
            (lift c') →
              c≡c'? c'
                {C = λ x →
                  ＂ c' ＂ ⊗ implicitFailCarrier litAut ⟦_⟧st (map-Maybe inr x) ⊢ ＂ c ＂
                }
                (λ c≡c' → transportG (cong ＂_＂ (sym c≡c')) ∘g ⊗-unit-r)
                (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ lowerG)
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            }
        })
      litAlg (just (inr _)) =
        ⊕ᴰ-elim (λ {
          stop → ⊕ᴰ-elim λ _ → lowerG ∘g lowerG
        ; step → ⊕ᴰ-elim (λ _ → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ (lowerG ∘g lowerG))
        })

      toDFA : ∀ q → ⟦ q ⟧st ⊢ Trace litDFA true (just q)
      toDFA (inl _) =
        STEP litDFA {q = just (inl _)} c
        ∘g id ,⊗
          transportG
            (cong (λ z → Trace litDFA true z)
              (elim-≡ c {C = λ x → just (inr tt) ≡ map-Maybe inr x} refl refl)
            )
        ∘g id ,⊗ STOP litDFA {q = just (inr _)}
        ∘g ⊗-unit-r⁻
      toDFA (inr _) = STOP litDFA

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
