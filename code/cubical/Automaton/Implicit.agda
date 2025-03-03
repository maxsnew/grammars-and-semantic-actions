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


FreelyAddFail→FreelyAddFail+Initial :
  ∀ {Q : Type ℓ} →
  FreelyAddFail Q →
  FreelyAddFail+Initial Q
FreelyAddFail→FreelyAddFail+Initial fail = fail
FreelyAddFail→FreelyAddFail+Initial (↑f q) = ↑q q

↑f→q = FreelyAddFail→FreelyAddFail+Initial

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

  -- open DeterministicAutomaton

  data Tag : Bool → (q : FreelyAddFail+Initial Q) → Type ℓ where
    stop : ∀ q → Tag (acc q) (↑q q)
    stopᵢ : Tag null initial
    stopFail : Tag false fail
    step : ∀ {b} (q : Q) → (c : ⟨ Alphabet ⟩) → Tag b (↑q q)
    stepᵢ : ∀ {b} → (c : ⟨ Alphabet ⟩) → Tag b initial
    -- step : ∀ {b} (q : Q) → (c : ⟨ Alphabet ⟩) → Eq.fiber ↑f_ (δq q c) → Tag b (↑q q)
    -- stepᵢ : ∀ {b} → (c : ⟨ Alphabet ⟩) → Eq.fiber ↑f_ (δᵢ c) → Tag b initial
    stepFail : ∀ {b} → (c : ⟨ Alphabet ⟩) → Tag b fail
    -- unexpected : ∀ q → (c : ⟨ Alphabet ⟩) → fail Eq.≡ δq q c → Tag false (↑q q)
    -- unexpectedᵢ : (c : ⟨ Alphabet ⟩) → fail Eq.≡ δᵢ c → Tag false initial

  TraceTy : Bool → (q : FreelyAddFail+Initial Q) → Functor (FreelyAddFail+Initial Q)
  TraceTy b q =
    ⊕e (Tag b q) λ where
      (stop q) → k ε*
      (stopᵢ) → k ε*
      (stopFail) → k ε*
      (step q c) → ⊗e (k (literal* c)) (Var (↑f→q (δq q c)))
      (stepᵢ c) → ⊗e (k (literal* c)) (Var (↑f→q (δᵢ c)))
      (stepFail c) → ⊗e (k (literal* c)) (Var fail)

  Trace : Bool → FreelyAddFail+Initial Q → Grammar _
  Trace b = μ (TraceTy b)

  STOP : (q : Q) → ε ⊢ Trace (acc q) (↑q q)
  STOP q =
    roll
    ∘g ⊕ᴰ-in (stop q)
    ∘g liftG ∘g liftG

  STOPᵢ : ε ⊢ Trace null initial
  STOPᵢ =
    roll
    ∘g ⊕ᴰ-in stopᵢ
    ∘g liftG ∘g liftG

  STOPFAIL : ε ⊢ Trace false fail
  STOPFAIL =
    roll
    ∘g ⊕ᴰ-in stopFail
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

  -- UNEXPECTED : (q : Q) → (c : ⟨ Alphabet ⟩) →
  --   fail Eq.≡ δq q c →
  --   ＂ c ＂ ⊗ Trace false fail ⊢ Trace false (↑q q)
  -- UNEXPECTED q c x =
  --   roll
  --   ∘g ⊕ᴰ-in (unexpected q c x)
  --   ∘g (liftG ∘g liftG) ,⊗ liftG

  -- UNEXPECTEDᵢ : (c : ⟨ Alphabet ⟩) →
  --   fail Eq.≡ δᵢ c →
  --   ＂ c ＂ ⊗ Trace false fail ⊢ Trace false initial
  -- UNEXPECTEDᵢ c x =
  --   roll
  --   ∘g ⊕ᴰ-in (unexpectedᵢ c x)
  --   ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace true initial

  -- TraceAlgCarrier :
  --   (A-init : Grammar ℓA) →
  --   (A-fail : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   FreelyAddFail+Initial Q →
  --   Grammar ℓA
  -- TraceAlgCarrier A-init A-fail A initial = A-init
  -- TraceAlgCarrier A-init A-fail A fail = A-fail
  -- TraceAlgCarrier A-init A-fail A (↑q q) = A q

  -- TraceAlg :
  --   (A-init : Grammar ℓA) →
  --   (A-fail : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   Bool → Type (ℓ-max ℓ ℓA)
  -- TraceAlg A-init A-fail A b =
  --   Algebra (TraceTy b) (TraceAlgCarrier A-init A-fail A)

  -- ParseAlgCarrier :
  --   (A-init : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   FreelyAddFail+Initial Q →
  --   Grammar ℓA
  -- ParseAlgCarrier A-init A = TraceAlgCarrier A-init ⊥* A

  -- ParseAlg :
  --   (A-init : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   Bool → Type (ℓ-max ℓ ℓA)
  -- ParseAlg A-init = TraceAlg A-init ⊥*

  -- ParseAlg-fail' :
  --   {A-init : Grammar ℓA} →
  --   {A : Q → Grammar ℓA} →
  --   ⟦ TraceTy true fail ⟧ (ParseAlgCarrier A-init A) ⊢ ⊥
  -- ParseAlg-fail' =
  --   ⊕ᴰ-elim λ where
  --     (stopFail ())

  -- ParseAlg-fail :
  --   {A-init : Grammar ℓA} →
  --   {A : Q → Grammar ℓA} →
  --   {B : Grammar ℓB} →
  --   ⟦ TraceTy true fail ⟧ (ParseAlgCarrier A-init A) ⊢ B
  -- ParseAlg-fail = ⊥-elim ∘g ParseAlg-fail'


  -- fail→false' : ∀ {b : Bool} → Trace b fail ⊢ ⊕[ x ∈ b Eq.≡ false ] Trace b fail
  -- fail→false' {b = b} = rec _ fail→falseAlg fail
  --   where
  --   fail→falseAlg : Algebra (TraceTy _)
  --     (λ where
  --       fail → ⊕[ x ∈ b Eq.≡ false ] Trace b fail
  --       initial → ⊤*
  --       (↑q q) → ⊤*
  --     )
  --   fail→falseAlg fail =
  --     ⊕ᴰ-elim λ where
  --       (stopFail) → ⊕ᴰ-in Eq.refl ∘g STOPFAIL ∘g lowerG ∘g lowerG
  --       (stepFail c) →
  --         map⊕ᴰ (λ where Eq.refl → STEPFAIL c)
  --         ∘g ⊕ᴰ-distR .fun
  --         ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  --   fail→falseAlg initial = ⊤*-intro
  --   fail→falseAlg (↑q q) = ⊤*-intro

  -- fail→false : ∀ {b : Bool} → Trace b fail ⊢ Trace false fail
  -- fail→false {b = b} =
  --   ⊕ᴰ-elim (λ where Eq.refl → id)
  --   ∘g fail→false'

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
      (stopFail) → NIL ∘g lowerG ∘g lowerG
      (stepFail c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  printAlg b initial =
    ⊕ᴰ-elim λ where
      (stopᵢ) → NIL ∘g lowerG ∘g lowerG
      (stepᵢ c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  printAlg b (↑q q) =
    ⊕ᴰ-elim λ where
      (stop .q) → NIL ∘g lowerG ∘g lowerG
      (step .q c) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  print : ∀ b q → Trace b q ⊢ string
  print b = rec _ (printAlg b)

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q =
    ⊕ᴰ-elim λ where
      (stop q) → ⊕ᴰ-in b ∘g STOP q ∘g lowerG ∘g lowerG
      (stopᵢ) → ⊕ᴰ-in b ∘g STOPᵢ ∘g lowerG ∘g lowerG
      (stopFail) → ⊕ᴰ-in b ∘g STOPFAIL ∘g lowerG ∘g lowerG
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
                 (stop q) → refl
                 (stopᵢ) → refl
                 (stopFail) → refl
                 (step q c) → refl
                 (stepᵢ c) → refl
                 (stepFail c) → refl
           )
          )
          ((λ q → ⊕ᴰ-in b) ,
           (λ q →
             ⊕ᴰ≡ _ _
               λ where
                 (stop q) → refl
                 stopᵢ → refl
                 stopFail → refl
                 (step q c) → refl
                 (stepᵢ c) → refl
                 (stepFail c) → refl
           )
          )
          q

  -- -- TraceParser : Parser {!!}
  -- -- TraceParser = {!!}

  -- -- Aut : DeterministicAutomaton (FreelyAddFail+Initial Q)
  -- -- Aut .init = initial
  -- -- Aut .isAcc fail = false
  -- -- Aut .isAcc initial = null
  -- -- Aut .isAcc (↑q q) = acc q
  -- -- Aut .δ fail _ = fail
  -- -- Aut .δ initial c with δᵢ c
  -- -- ... | fail = fail
  -- -- ... | ↑f q = ↑q q
  -- -- -- FreelyAddFail→FreelyAddFail+Initial (δᵢ c)
  -- -- Aut .δ (↑q q) c with δq q c
  -- -- ... | fail = fail
  -- -- ... | ↑f q = ↑q q

  -- -- AutAlgCarrier :
  -- --   (A-init : Grammar ℓA) →
  -- --   (A : Q → Grammar ℓA) →
  -- --   FreelyAddFail+Initial Q →
  -- --   Grammar ℓA
  -- -- AutAlgCarrier A-init A fail = ⊥*
  -- -- AutAlgCarrier A-init A initial = A-init
  -- -- AutAlgCarrier A-init A (↑q q) = A q

  -- -- AutAlg :
  -- --   (A-init : Grammar ℓA) →
  -- --   (A : Q → Grammar ℓA) →
  -- --   Type (ℓ-max ℓ ℓA)
  -- -- AutAlg A-init A = ParseAlg Aut (AutAlgCarrier A-init A)

  -- -- AutAlg-fail' :
  -- --   {A-init : Grammar ℓA} →
  -- --   {A : Q → Grammar ℓA} →
  -- --   ⟦ TraceTy Aut true fail ⟧ (AutAlgCarrier A-init A) ⊢ ⊥
  -- -- AutAlg-fail' =
  -- --   ⊕ᴰ-elim (λ {
  -- --     step → ⊕ᴰ-elim (λ _ → ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG))
  -- --   })

  -- -- AutAlg-fail :
  -- --   {A-init : Grammar ℓA} →
  -- --   {A : Q → Grammar ℓA} →
  -- --   {B : Grammar ℓB} →
  -- --   ⟦ TraceTy Aut true fail ⟧ (AutAlgCarrier A-init A) ⊢ B
  -- -- AutAlg-fail = ⊥-elim ∘g AutAlg-fail'

  -- -- noMapsIntoInitial' :
  -- --   ∀ (q : FreelyAddFail+Initial Q)  →
  -- --   (c : ⟨ Alphabet ⟩) →
  -- --   fiber ↑q_ (Aut .δ q c) ⊎ (Aut .δ q c ≡ fail)
  -- -- noMapsIntoInitial' fail c = inr refl
  -- -- noMapsIntoInitial' initial c with δᵢ c
  -- -- noMapsIntoInitial' initial c | fail = inr refl
  -- -- noMapsIntoInitial' initial c | ↑f q = inl (q , refl)
  -- -- noMapsIntoInitial' (↑q q) c with δq q c
  -- -- noMapsIntoInitial' (↑q q) c | fail = inr refl
  -- -- noMapsIntoInitial' (↑q q) c | ↑f q' = inl (q' , refl)
