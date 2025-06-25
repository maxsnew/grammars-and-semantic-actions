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

open import SemanticAction.Base Alphabet
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

  Ix-f : Maybe ℕ → Functor Unit
  Ix-f nothing  = ⊕e Empty.⊥ λ ()
  Ix-f (just n) = Var _ ⊗e Closers n

  module _ (A : Unit → Grammar ℓ-zero) (α : Algebra DyckF A) where
    step-[ : ∀ n →
      (literal [) ⊗ (⟦ Ix-f (just (suc n)) ⟧ A)
      ⊢ ⟦ Var tt ⊗e Closers n ⟧ A
    step-[ _ = (α _ ∘g σ balanced') ,⊗ id ∘g ⊗-assoc4

    Str-f : Algebra (CountParens.AccTraceF true) (λ bn? → ⟦ Ix-f bn? ⟧ A )
    -- TODO: this could be done generically if we made δ : State → Alphabet → Maybe State
    Str-f nothing = ⊕ᴰ-elim (λ where
      (CountParens.step c) → ⊕ᴰ-elim (λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    -- This is specific to LL grammars
    Str-f (just zero) = ⊕ᴰ-elim (λ where
      -- interesting: the nil case is the same as the close case for the other state...
      (CountParens.stop _) → (α _ ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻
      (CountParens.step [) → step-[ zero
      (CountParens.step ]) → (⊕ᴰ-elim λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    Str-f (just (suc n)) = ⊕ᴰ-elim (λ where
      (CountParens.step [) → step-[ $ suc n
      (CountParens.step ]) → (α _ ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻)

  opaque
    unfolding ⊗-intro ⊕ᴰ-distR ⊗-unit-l⁻
    Str-f-homo : ∀ {A B α β}
      (ϕ : Homomorphism DyckF α β)
      → isHomo (CountParens.AccTraceF true) (Str-f A α) (Str-f B β) λ bn? → map (Ix-f bn?) (ϕ .fst)
    Str-f-homo ϕ nothing = ⊕ᴰ≡ _ _ λ where
      (CountParens.step c) → uninhabited→PropHoms ((⊕ᴰ-elim λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    Str-f-homo ϕ (just zero) = ⊕ᴰ≡ _ _ λ where
      (CountParens.stop _) → λ i → (ϕ .snd _ i ∘g σ nil') ,⊗ id ∘g ⊗-unit-l⁻
      (CountParens.step [) → λ i → (ϕ .snd _ i ∘g σ balanced') ,⊗ id ∘g ⊗-assoc4
      (CountParens.step ]) → uninhabited→PropHoms ((⊕ᴰ-elim λ ()) ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
    Str-f-homo {α = α}{β} ϕ (just (suc n)) = ⊕ᴰ≡ _ _ λ where
      (CountParens.step [) → λ i → (ϕ .snd _ i ∘g σ balanced') ,⊗ map (Closers (suc n)) (ϕ .fst) ∘g ⊗-assoc4
      (CountParens.step ]) →
        (λ i → (ϕ .snd _ i ∘g σ nil') ,⊗ map (Closers (suc n)) (ϕ .fst) ∘g ⊗-unit-l⁻)

Trace→Dyck : StructureTransform
  (mkStructure (CountParens.AccTraceF true))
  DyckStr
Trace→Dyck = mkStructureTransform Ix-f Str-f λ α β → Str-f-homo

String→Dyck : StructureTransform
  (mkStructure StrF)
  DyckStr
String→Dyck =
  Trace→Dyck
  ∘str (CountParens.markAccept
  ∘str CountParens.parseTrace)

module String→Dyck = StructureTransform String→Dyck

-- doesn't actually matter that X is pure here but it corresponds to a
-- semantic action
module _ {X} (semAct : Algebra DyckF (λ _ → Pure X)) where
  parseDyck :
      μ StrF _
      ⊢ (⊕ᴰ {X = Bool} λ where
          false → μ (CountParens.AccTraceF false) (just 0)
          true → Pure X)
  parseDyck =
    (map⊕ᴰ λ where
      false → id
      true → ⊗-unit-r)
    ∘g π (just 0)
    ∘g String→Dyck.toFold semAct _

  -- Should be able to prove this but getting stuck with Agda's
  -- nominal λ nonsense

  -- parseDyck-fusion :
  --   parseDyck
  --   ≡ ((map⊕ᴰ λ where
  --        false → id
  --        true → rec DyckF semAct _ ∘g ⊗-unit-r))
  --     ∘g π (just 0)
  --     ∘g String→Dyck.toFoldToTrees _
  -- parseDyck-fusion =
  --   (λ i → (map⊕ᴰ λ where
  --     false → id
  --     true → ⊗-unit-r)
  --   ∘g π (just 0)
  --   ∘g {!(String→Dyck.toFold-fusion semAct) (~ i) _!})
  --   ∙ {!!}
