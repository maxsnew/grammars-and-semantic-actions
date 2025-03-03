{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Automaton.Implicit (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Sum as Sum hiding (rec)
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Grammar.SequentialUnambiguity Alphabet
open import Term Alphabet

open import Automaton.Deterministic Alphabet
open import Parser.Base Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' ℓA ℓB : Level

data FreelyAddInitial (Q : Type ℓ) : Type ℓ where
  initial : FreelyAddInitial Q
  ↑i_ : Q → FreelyAddInitial Q

data FreelyAddFail (Q : Type ℓ) : Type ℓ where
  fail : FreelyAddFail Q
  ↑f_ : Q → FreelyAddFail Q

data FreelyAddFail+Initial (Q : Type ℓ) : Type ℓ where
  fail initial : FreelyAddFail+Initial Q
  ↑q_ : Q → FreelyAddFail+Initial Q

FreelyAddInitial→FreelyAddFail+Initial :
  ∀ {Q : Type ℓ} →
  FreelyAddInitial Q →
  FreelyAddFail+Initial Q
FreelyAddInitial→FreelyAddFail+Initial initial = initial
FreelyAddInitial→FreelyAddFail+Initial (↑i q) = ↑q q

FreelyAddFail→FreelyAddFail+Initial :
  ∀ {Q : Type ℓ} →
  FreelyAddFail Q →
  FreelyAddFail+Initial Q
FreelyAddFail→FreelyAddFail+Initial fail = fail
FreelyAddFail→FreelyAddFail+Initial (↑f q) = ↑q q

↑f→q = FreelyAddFail→FreelyAddFail+Initial
↑i→q = FreelyAddInitial→FreelyAddFail+Initial

module _ {Q : Type ℓ} where
  fail≢↑f : ∀ {q : Q} → fail Eq.≡ ↑f q → Empty.⊥
  fail≢↑f ()

module _ (Q : Type ℓ) where
  open Iso
  FreelyAddInitial≅Unit⊎ : Iso (FreelyAddInitial Q) (Unit ⊎ Q)
  FreelyAddInitial≅Unit⊎ .fun initial = inl _
  FreelyAddInitial≅Unit⊎ .fun (↑i q) = inr q
  FreelyAddInitial≅Unit⊎ .inv (inl _) = initial
  FreelyAddInitial≅Unit⊎ .inv (inr q) = ↑i q
  FreelyAddInitial≅Unit⊎ .rightInv (inl _) = refl
  FreelyAddInitial≅Unit⊎ .rightInv (inr _) = refl
  FreelyAddInitial≅Unit⊎ .leftInv initial = refl
  FreelyAddInitial≅Unit⊎ .leftInv (↑i _) = refl

  FreelyAddFail≅Unit⊎ : Iso (FreelyAddFail Q) (Unit ⊎ Q)
  FreelyAddFail≅Unit⊎ .fun fail = inl _
  FreelyAddFail≅Unit⊎ .fun (↑f q) = inr q
  FreelyAddFail≅Unit⊎ .inv (inl _) = fail
  FreelyAddFail≅Unit⊎ .inv (inr q) = ↑f q
  FreelyAddFail≅Unit⊎ .rightInv (inl _) = refl
  FreelyAddFail≅Unit⊎ .rightInv (inr _) = refl
  FreelyAddFail≅Unit⊎ .leftInv fail = refl
  FreelyAddFail≅Unit⊎ .leftInv (↑f _) = refl

  FreelyAddFail+Initial≅Unit⊎Unit⊎ : Iso (FreelyAddFail+Initial Q) ((Unit ⊎ Unit) ⊎ Q)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun initial = inl (inl _)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun fail = inl (inr _)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun (↑q q) = inr q
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (inl (inl _)) = initial
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (inl (inr _)) = fail
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (inr q) = ↑q q
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .rightInv (inl (inl _)) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .rightInv (inl (inr _)) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .rightInv (inr _) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .leftInv fail = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .leftInv initial = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .leftInv (↑q _) = refl

-- Automata with a transition function given partially such
-- that unspecified transitions implicitly map to a fail state
-- Further, these have a freely added initial state such that
-- there are no back edges to the initial state
record ImplicitDeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor mkImplicitAut
  field
    acc : Q → Bool
    null : Bool
    δq : Q → ⟨ Alphabet ⟩ → FreelyAddFail Q -- transitions between internal states
    δᵢ : ⟨ Alphabet ⟩ → FreelyAddFail Q -- transitions out of the initial state

  data Tag (b : Bool) : (q : FreelyAddFail+Initial Q) → Type ℓ where
    stop : ∀ q → b Eq.≡ acc q → Tag b (↑q q)
    stopᵢ : b Eq.≡ null → Tag b initial
    stopFail : b Eq.≡ false → Tag b fail
    step : (q : Q) → (c : ⟨ Alphabet ⟩) → Tag b (↑q q)
    stepᵢ : (c : ⟨ Alphabet ⟩) → Tag b initial
    stepFail : (c : ⟨ Alphabet ⟩) → Tag b fail

  TraceTy : Bool → (q : FreelyAddFail+Initial Q) → Functor (FreelyAddFail+Initial Q)
  TraceTy b q =
    ⊕e (Tag b q) λ where
      (stop q x) → k ε*
      (stopᵢ x) → k ε*
      (stopFail x) → k ε*
      (step q c) → ⊗e (k (literal* c)) (Var (↑f→q (δq q c)))
      (stepᵢ c) → ⊗e (k (literal* c)) (Var (↑f→q (δᵢ c)))
      (stepFail c) → ⊗e (k (literal* c)) (Var fail)

  Trace : Bool → FreelyAddFail+Initial Q → Grammar _
  Trace b = μ (TraceTy b)

  TraceAlg : Bool → (FreelyAddFail+Initial Q → Grammar ℓA) → Type (ℓ-max ℓ ℓA)
  TraceAlg b = Algebra (TraceTy b)

  module _ (A : FreelyAddInitial Q → Grammar ℓA) where
    ParseAlgCarrier : FreelyAddFail+Initial Q → Grammar ℓA
    ParseAlgCarrier =
      λ where
        fail → ⊥*
        initial → A initial
        (↑q q) → A (↑i q)

    ParseAlg : Type (ℓ-max ℓ ℓA)
    ParseAlg = Algebra (TraceTy true) ParseAlgCarrier

    ParseAlgFail' : ⟦ TraceTy true fail ⟧ ParseAlgCarrier ⊢ ⊥
    ParseAlgFail' =
      ⊕ᴰ-elim λ where
        (stepFail c) → ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG)

    ParseAlgFail : {B : Grammar ℓB} → ⟦ TraceTy true fail ⟧ ParseAlgCarrier ⊢ B
    ParseAlgFail = ⊥-elim ∘g ParseAlgFail'

  STOP : (q : Q) → ε ⊢ Trace (acc q) (↑q q)
  STOP q =
    roll
    ∘g ⊕ᴰ-in (stop q Eq.refl)
    ∘g liftG ∘g liftG

  STOPᵢ : ε ⊢ Trace null initial
  STOPᵢ =
    roll
    ∘g ⊕ᴰ-in (stopᵢ Eq.refl)
    ∘g liftG ∘g liftG

  STOPFAIL : ε ⊢ Trace false fail
  STOPFAIL =
    roll
    ∘g ⊕ᴰ-in (stopFail Eq.refl)
    ∘g liftG ∘g liftG

  STEP : ∀ {b : Bool} → (q : Q) → (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace b (↑f→q (δq q c)) ⊢ Trace b (↑q q)
  STEP q c =
    roll
    ∘g ⊕ᴰ-in (step q c)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPᵢ : ∀ {b : Bool} → (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace b (↑f→q (δᵢ c)) ⊢ Trace b initial
  STEPᵢ c =
    roll
    ∘g ⊕ᴰ-in (stepᵢ c)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPFAIL : ∀ {b : Bool} → (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace b fail ⊢ Trace b fail
  STEPFAIL c =
    roll
    ∘g ⊕ᴰ-in (stepFail c)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace true initial

  readAlg : Algebra (*Ty char) λ _ → &[ q ∈ FreelyAddFail+Initial Q ] ⊕[ b ∈ Bool ] Trace b q
  readAlg _ =
    ⊕ᴰ-elim λ where
      nil →
        (&ᴰ-in λ where
           fail → ⊕ᴰ-in false ∘g STOPFAIL
           initial → ⊕ᴰ-in null ∘g STOPᵢ
           (↑q q) → ⊕ᴰ-in (acc q) ∘g STOP q
        )
        ∘g lowerG ∘g lowerG
      cons →
        (&ᴰ-in λ where
          fail →
            ⊕ᴰ-elim (λ c →
              map⊕ᴰ (λ b → STEPFAIL c)
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π fail
            )
          initial →
            ⊕ᴰ-elim (λ c →
              map⊕ᴰ (λ b → STEPᵢ c)
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π (↑f→q (δᵢ c))
            )
          (↑q q) →
            ⊕ᴰ-elim (λ c →
              map⊕ᴰ (λ b → STEP q c)
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π (↑f→q (δq q c))
            )
        )
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG ,⊗ lowerG

  read : string ⊢ &[ q ∈ FreelyAddFail+Initial Q ] ⊕[ b ∈ Bool ] Trace b q
  read = rec _ readAlg _

  printAlg : ∀ b → Algebra (TraceTy b) λ _ → string
  printAlg b fail =
    ⊕ᴰ-elim λ where
      (stopFail x) → NIL ∘g lowerG ∘g lowerG
      (stepFail c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  printAlg b initial =
    ⊕ᴰ-elim λ where
      (stopᵢ x) → NIL ∘g lowerG ∘g lowerG
      (stepᵢ c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  printAlg b (↑q q) =
    ⊕ᴰ-elim λ where
      (stop .q x) → NIL ∘g lowerG ∘g lowerG
      (step .q c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  print : ∀ b q → Trace b q ⊢ string
  print b = rec _ (printAlg b)

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q =
    ⊕ᴰ-elim λ where
      (stop q Eq.refl) →
        ⊕ᴰ-in (acc q) ∘g STOP q ∘g lowerG ∘g lowerG
      (stopᵢ Eq.refl) →
        ⊕ᴰ-in null ∘g STOPᵢ ∘g lowerG ∘g lowerG
      (stopFail Eq.refl) →
        ⊕ᴰ-in false ∘g STOPFAIL ∘g lowerG ∘g lowerG
      (step q c) →
        ⊕ᴰ-elim (λ b' → ⊕ᴰ-in b' ∘g STEP q c)
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (stepᵢ c) →
        ⊕ᴰ-elim (λ b' → ⊕ᴰ-in b' ∘g STEPᵢ c)
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (stepFail c) →
        map⊕ᴰ (λ b → STEPFAIL c)
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  Trace≅string : (q : FreelyAddFail+Initial Q) → (⊕[ b ∈ Bool ] Trace b q) ≅ string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = &ᴰ-π q ∘g read
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      the-ret : &ᴰ-π q ∘g read ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      the-ret = ⊕ᴰ≡ _ _ λ b →
        ind'
          (TraceTy b)
          (⊕ᴰAlg b)
          ((λ q → &ᴰ-π q ∘g read ∘g print b q) ,
           (λ q →
             ⊕ᴰ≡ _ _
               λ where
                 (stop q Eq.refl) → refl
                 (stopᵢ Eq.refl) → refl
                 (stopFail Eq.refl) → refl
                 (step q c) → refl
                 (stepᵢ c) → refl
                 (stepFail c) → refl
           )
          )
          ((λ q → ⊕ᴰ-in b) ,
           (λ q →
             ⊕ᴰ≡ _ _
               λ where
                 (stop q Eq.refl) → refl
                 (stopᵢ Eq.refl) → refl
                 (stopFail Eq.refl) → refl
                 (step q c) → refl
                 (stepᵢ c) → refl
                 (stepFail c) → refl
           )
          )
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q = unambiguous≅ (sym≅ (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b

  fail→false' : ∀ {b : Bool} → Trace b fail ⊢ ⊕[ x ∈ b Eq.≡ false ] Trace b fail
  fail→false' {b = b} = rec _ fail→falseAlg fail
    where
    fail→falseAlg : Algebra (TraceTy _)
      (λ where
        fail → ⊕[ x ∈ b Eq.≡ false ] Trace b fail
        initial → ⊤*
        (↑q q) → ⊤*
      )
    fail→falseAlg fail =
      ⊕ᴰ-elim λ where
        (stopFail Eq.refl) → ⊕ᴰ-in Eq.refl ∘g STOPFAIL ∘g lowerG ∘g lowerG
        (stepFail c) →
          map⊕ᴰ (λ where Eq.refl → STEPFAIL c)
          ∘g ⊕ᴰ-distR .fun
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
    fail→falseAlg initial = ⊤*-intro
    fail→falseAlg (↑q q) = ⊤*-intro

  fail→false : ∀ {b : Bool} → Trace b fail ⊢ Trace false fail
  fail→false {b = b} =
    ⊕ᴰ-elim (λ where Eq.refl → id)
    ∘g fail→false'

  open Parser
  AcceptingTraceParser : ∀ q → Parser (Trace true q)
  AcceptingTraceParser q .compl = Trace false q
  AcceptingTraceParser q .compl-disjoint =
    hasDisjointSummands⊕ᴰ isSetBool (unambiguous-⊕Trace q)
      true false true≢false
  AcceptingTraceParser q .fun =
    ⊕ᴰ-elim (
      λ where
        true → ⊕-inl
        false → ⊕-inr
    )
    ∘g &ᴰ-π q ∘g read

  getFirstTransition :
    ∀ (c : ⟨ Alphabet ⟩) →
    startsWith c & Parse ⊢ ⊕[ x ∈ fiber ↑f_ (δᵢ c) ] ⊤
  getFirstTransition c =
    ⇒-intro⁻ (rec _ the-alg initial)
    ∘g &-swap
    where
    ⟦_⟧q : FreelyAddInitial Q → Grammar _
    ⟦ initial ⟧q = startsWith c ⇒ (⊕[ _ ∈ fiber ↑f_ (δᵢ c) ] ⊤)
    ⟦ ↑i q ⟧q = ⊤*

    the-alg : ParseAlg ⟦_⟧q
    the-alg fail = ParseAlgFail _
    the-alg initial =
      ⊕ᴰ-elim λ where
        (stopᵢ x) →
          ⇒-intro (⊥-elim ∘g ¬Nullable-startsWith) ∘g lowerG ∘g lowerG
        (stepᵢ c') →
          help c'
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      where
      help : (c' : ⟨ Alphabet ⟩) → ＂ c' ＂ ⊗ ParseAlgCarrier ⟦_⟧q (↑f→q (δᵢ c')) ⊢ ParseAlgCarrier ⟦_⟧q initial
      help c' with δᵢ c' in eq
      ... | fail = ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim
      ... | ↑f q =
        ⇒-intro
          (⊕ᴰ-elim (λ c'≡c →
             ⊕ᴰ-in (q , (J (λ c'' c≡c'' → (↑f q) ≡ δᵢ c'') (Eq.eqToPath (Eq.sym eq)) c'≡c))
             ∘g ⊤-intro
          )
          ∘g same-first' c' c
          ∘g (id ,⊗ string-intro) ,&p (id ,⊗ string-intro)
          )

    the-alg (↑q q) =
      ⊕ᴰ-elim λ where
        (stop .q x) → ⊤*-intro
        (step .q c) → ⊤*-intro

  ¬FirstAut :
    (c : ⟨ Alphabet ⟩) →
    fail ≡ δᵢ c →
    ⟨ c ∉First Parse ⟩
  ¬FirstAut c toFail =
    ⊕ᴰ-elim (λ { (q , x) → Empty.rec (fail≢↑f (Eq.pathToEq (toFail ∙ sym x))) })
    ∘g getFirstTransition c

  sound-null :
    Parse & ε ⊢ ⊕[ _ ∈ true ≡ null ] ⊤
  sound-null =
    map⊕ᴰ (λ _ → ⊤-intro)
    ∘g ⊕ᴰ-fst≡ _ _ _ _
        (unambiguous-⊕Trace initial
          (⊕ᴰ-in true ∘g &-π₁)
          (⊕ᴰ-in null ∘g &-π₂)
        )
    ∘g id ,&p STOPᵢ

  ¬NullableAut :
    null ≡ false →
    ⟨ ¬Nullable Parse ⟩
  ¬NullableAut isFalse =
    ⊕ᴰ-elim (λ isTrue → Empty.rec (true≢false (isTrue ∙ isFalse)))
    ∘g sound-null
    ∘g &-swap
