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

module _ (Q : Type ℓ) where
  -- elimFreelyAddFail :
  --   {B : FreelyAddFail Q → Type ℓ'} →
  --   B fail →
  --   ((q : Q) → B (↑f q)) →
  --   (q : FreelyAddFail Q) →
  --   B q
  -- elimFreelyAddFail if-fail if-↑f fail = if-fail
  -- elimFreelyAddFail if-fail if-↑f (↑f x) = if-↑f x

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

  data Tag (b : Bool) : (q : FreelyAddFail+Initial Q) → Type ℓ where
    stop : ∀ q → b Eq.≡ acc q → Tag b (↑q q)
    stopᵢ : b Eq.≡ null → Tag b initial
    stopFail : b Eq.≡ false → Tag b fail
    step : ∀ q → (c : ⟨ Alphabet ⟩) → Eq.fiber ↑f_ (δq q c) → Tag b (↑q q)
    stepᵢ : (c : ⟨ Alphabet ⟩) → Eq.fiber ↑f_ (δᵢ c) → Tag b initial
    stepFail : (c : ⟨ Alphabet ⟩) → b Eq.≡ false → Tag b fail
    unexpected : ∀ q → (c : ⟨ Alphabet ⟩) → b Eq.≡ false → fail Eq.≡ δq q c → Tag b (↑q q)
    unexpectedᵢ : (c : ⟨ Alphabet ⟩) → b Eq.≡ false → fail Eq.≡ δᵢ c → Tag b initial

  TraceTy : Bool → (q : FreelyAddFail+Initial Q) → Functor (FreelyAddFail+Initial Q)
  TraceTy b q =
    ⊕e (Tag b q) λ where
      (stop q acc) → k ε*
      (stopᵢ isNull) → k ε*
      (stopFail x) → k ε*
      (step q c (q' , x)) → ⊗e (k (literal* c)) (Var (↑q q'))
      (stepᵢ c (q' , x)) → ⊗e (k (literal* c)) (Var (↑q q'))
      (stepFail c x) → ⊗e (k (literal* c)) (k (LiftG ℓ string))
      (unexpected q c isFalse x) → ⊗e (k (literal* c)) (Var fail)
      (unexpectedᵢ c isFalse x) → ⊗e (k (literal* c)) (Var fail)

  Trace : Bool → FreelyAddFail+Initial Q → Grammar _
  Trace b = μ (TraceTy b)

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
    (fib : Eq.fiber ↑f_ (δq q c)) →
    ＂ c ＂ ⊗ Trace b (↑q (fib .fst)) ⊢ Trace b (↑q q)
  STEP q c fib =
    roll
    ∘g ⊕ᴰ-in (step q c fib)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPᵢ : ∀ {b : Bool} → (c : ⟨ Alphabet ⟩) →
    (fib : Eq.fiber ↑f_ (δᵢ c)) →
    ＂ c ＂ ⊗ Trace b (↑q (fib .fst)) ⊢ Trace b initial
  STEPᵢ c fib =
    roll
    ∘g ⊕ᴰ-in (stepᵢ c fib)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPFAIL : ∀ {b : Bool} → (c : ⟨ Alphabet ⟩) →
    b Eq.≡ false →
    ＂ c ＂ ⊗ string ⊢ Trace b fail
  STEPFAIL c isFalse =
    roll
    ∘g ⊕ᴰ-in (stepFail c isFalse)
    ∘g (liftG ∘g liftG) ,⊗ (liftG ∘g liftG)

  UNEXPECTED : ∀ {b : Bool} → (q : Q) → (c : ⟨ Alphabet ⟩) →
    b Eq.≡ false →
    fail Eq.≡ δq q c →
    ＂ c ＂ ⊗ Trace b fail ⊢ Trace b (↑q q)
  UNEXPECTED q c Eq.refl x =
    roll
    ∘g ⊕ᴰ-in (unexpected q c Eq.refl x)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  UNEXPECTEDᵢ : ∀ {b : Bool} → (c : ⟨ Alphabet ⟩) →
    b Eq.≡ false →
    fail Eq.≡ δᵢ c →
    ＂ c ＂ ⊗ Trace b fail ⊢ Trace b initial
  UNEXPECTEDᵢ c Eq.refl x =
    roll
    ∘g ⊕ᴰ-in (unexpectedᵢ c Eq.refl x)
    ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace true initial

  TraceAlgCarrier :
    (A-init : Grammar ℓA) →
    (A-fail : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    FreelyAddFail+Initial Q →
    Grammar ℓA
  TraceAlgCarrier A-init A-fail A initial = A-init
  TraceAlgCarrier A-init A-fail A fail = A-fail
  TraceAlgCarrier A-init A-fail A (↑q q) = A q

  TraceAlg :
    (A-init : Grammar ℓA) →
    (A-fail : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    Bool → Type (ℓ-max ℓ ℓA)
  TraceAlg A-init A-fail A b =
    Algebra (TraceTy b) (TraceAlgCarrier A-init A-fail A)

  ParseAlgCarrier :
    (A-init : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    FreelyAddFail+Initial Q →
    Grammar ℓA
  ParseAlgCarrier A-init A = TraceAlgCarrier A-init ⊥* A

  ParseAlg :
    (A-init : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    Bool → Type (ℓ-max ℓ ℓA)
  ParseAlg A-init = TraceAlg A-init ⊥*

  ParseAlg-fail' :
    {A-init : Grammar ℓA} →
    {A : Q → Grammar ℓA} →
    ⟦ TraceTy true fail ⟧ (ParseAlgCarrier A-init A) ⊢ ⊥
  ParseAlg-fail' =
    ⊕ᴰ-elim λ where
      (stopFail ())

  ParseAlg-fail :
    {A-init : Grammar ℓA} →
    {A : Q → Grammar ℓA} →
    {B : Grammar ℓB} →
    ⟦ TraceTy true fail ⟧ (ParseAlgCarrier A-init A) ⊢ B
  ParseAlg-fail = ⊥-elim ∘g ParseAlg-fail'


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
        (stepFail c Eq.refl) → ⊕ᴰ-in Eq.refl ∘g STEPFAIL c Eq.refl ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
    fail→falseAlg initial = ⊤*-intro
    fail→falseAlg (↑q q) = ⊤*-intro

  fail→false : ∀ {b : Bool} → Trace b fail ⊢ Trace false fail
  fail→false {b = b} =
    ⊕ᴰ-elim (λ where Eq.refl → id)
    ∘g fail→false'

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
              ⊕ᴰ-elim (λ b → ⊕ᴰ-in false ∘g STEPFAIL c Eq.refl ∘g id ,⊗ string-intro)
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π fail
            )
          initial →
            ⊕ᴰ-elim (λ c →
              ⊕ᴰ-elim (λ b →
                initialStep c b
              )
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π (FreelyAddFail→FreelyAddFail+Initial (δᵢ c))
            )
          (↑q q) →
            ⊕ᴰ-elim (λ c →
              ⊕ᴰ-elim (λ b →
                internalStep q c b
              )
              ∘g ⊕ᴰ-distR .fun
              ∘g id ,⊗ &ᴰ-π (FreelyAddFail→FreelyAddFail+Initial (δq q c))
            )
        )
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG ,⊗ lowerG
    where
    initialStep : (c : ⟨ Alphabet ⟩) → (b : Bool) →
      ＂ c ＂ ⊗ Trace b (FreelyAddFail→FreelyAddFail+Initial (δᵢ c))
        ⊢
      (⊕[ b ∈ Bool ] Trace b initial)
    initialStep c b with δᵢ c in eq
    ... | fail = ⊕ᴰ-in false ∘g UNEXPECTEDᵢ c Eq.refl (Eq.sym eq) ∘g id ,⊗ fail→false
    ... | ↑f q = ⊕ᴰ-in b ∘g STEPᵢ c (q , (Eq.sym eq))

    internalStep : (q : Q) → (c : ⟨ Alphabet ⟩) → (b : Bool) →
      ＂ c ＂ ⊗ Trace b (FreelyAddFail→FreelyAddFail+Initial (δq q c))
        ⊢
      (⊕[ b ∈ Bool ] Trace b (↑q q))
    internalStep q c b with δq q c in eq
    ... | fail = ⊕ᴰ-in false ∘g UNEXPECTED q c Eq.refl (Eq.sym eq) ∘g id ,⊗ fail→false
    ... | ↑f q' = ⊕ᴰ-in b ∘g STEP q c (q' , (Eq.sym eq))

  read : string ⊢ &[ q ∈ FreelyAddFail+Initial Q ] ⊕[ b ∈ Bool ] Trace b q
  read = rec _ readAlg _

  printAlg : ∀ b → Algebra (TraceTy b) λ _ → string
  printAlg b fail =
    ⊕ᴰ-elim λ where
      (stopFail x) → NIL ∘g lowerG ∘g lowerG
      (stepFail c x) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
  printAlg b initial =
    ⊕ᴰ-elim λ where
      (stopᵢ x) → NIL ∘g lowerG ∘g lowerG
      (stepᵢ c x) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (unexpectedᵢ c x x₁) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  printAlg b (↑q q) =
    ⊕ᴰ-elim λ where
      (stop .q x) → NIL ∘g lowerG ∘g lowerG
      (step .q c x) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (unexpected .q c x x₁) → CONS ∘g literal→char c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  print : ∀ b q → Trace b q ⊢ string
  print b = rec _ (printAlg b)

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q =
    ⊕ᴰ-elim λ where
      (stop q Eq.refl) → ⊕ᴰ-in b ∘g STOP q ∘g lowerG ∘g lowerG
      (stopᵢ Eq.refl) → ⊕ᴰ-in b ∘g STOPᵢ ∘g lowerG ∘g lowerG
      (stopFail Eq.refl) → ⊕ᴰ-in b ∘g STOPFAIL ∘g lowerG ∘g lowerG
      (step q c (q' , x)) →
        ⊕ᴰ-elim (λ b' → ⊕ᴰ-in b' ∘g STEP q c (q' , x))
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (stepᵢ c (q' , x)) →
        ⊕ᴰ-elim (λ b' → ⊕ᴰ-in b' ∘g STEPᵢ c (q' , x))
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (stepFail c Eq.refl) →
        ⊕ᴰ-in b
        ∘g STEPFAIL c Eq.refl
        ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
      (unexpected q c Eq.refl x) →
        ⊕ᴰ-elim (λ _ → ⊕ᴰ-in false ∘g UNEXPECTED q c Eq.refl x ∘g id ,⊗ fail→false)
        ∘g ⊕ᴰ-distR .fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      (unexpectedᵢ c Eq.refl x) →
        ⊕ᴰ-elim (λ _ → ⊕ᴰ-in false ∘g UNEXPECTEDᵢ c Eq.refl x ∘g id ,⊗ fail→false)
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
                 (step q c x) → {!!}
                 (stepᵢ c x) → {!!}
                 (stepFail c Eq.refl) → {!refl!}
                 (unexpected q c Eq.refl x) → {!refl!}
                 (unexpectedᵢ c Eq.refl x) → {!!}
           )
          )
          ({!!} ,
          {!!})
          q

  -- TraceParser : Parser {!!}
  -- TraceParser = {!!}

  -- Aut : DeterministicAutomaton (FreelyAddFail+Initial Q)
  -- Aut .init = initial
  -- Aut .isAcc fail = false
  -- Aut .isAcc initial = null
  -- Aut .isAcc (↑q q) = acc q
  -- Aut .δ fail _ = fail
  -- Aut .δ initial c with δᵢ c
  -- ... | fail = fail
  -- ... | ↑f q = ↑q q
  -- -- FreelyAddFail→FreelyAddFail+Initial (δᵢ c)
  -- Aut .δ (↑q q) c with δq q c
  -- ... | fail = fail
  -- ... | ↑f q = ↑q q

  -- AutAlgCarrier :
  --   (A-init : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   FreelyAddFail+Initial Q →
  --   Grammar ℓA
  -- AutAlgCarrier A-init A fail = ⊥*
  -- AutAlgCarrier A-init A initial = A-init
  -- AutAlgCarrier A-init A (↑q q) = A q

  -- AutAlg :
  --   (A-init : Grammar ℓA) →
  --   (A : Q → Grammar ℓA) →
  --   Type (ℓ-max ℓ ℓA)
  -- AutAlg A-init A = ParseAlg Aut (AutAlgCarrier A-init A)

  -- AutAlg-fail' :
  --   {A-init : Grammar ℓA} →
  --   {A : Q → Grammar ℓA} →
  --   ⟦ TraceTy Aut true fail ⟧ (AutAlgCarrier A-init A) ⊢ ⊥
  -- AutAlg-fail' =
  --   ⊕ᴰ-elim (λ {
  --     step → ⊕ᴰ-elim (λ _ → ⊗⊥ ∘g id ,⊗ (⊥*-elim ∘g lowerG))
  --   })

  -- AutAlg-fail :
  --   {A-init : Grammar ℓA} →
  --   {A : Q → Grammar ℓA} →
  --   {B : Grammar ℓB} →
  --   ⟦ TraceTy Aut true fail ⟧ (AutAlgCarrier A-init A) ⊢ B
  -- AutAlg-fail = ⊥-elim ∘g AutAlg-fail'

  -- noMapsIntoInitial' :
  --   ∀ (q : FreelyAddFail+Initial Q)  →
  --   (c : ⟨ Alphabet ⟩) →
  --   fiber ↑q_ (Aut .δ q c) ⊎ (Aut .δ q c ≡ fail)
  -- noMapsIntoInitial' fail c = inr refl
  -- noMapsIntoInitial' initial c with δᵢ c
  -- noMapsIntoInitial' initial c | fail = inr refl
  -- noMapsIntoInitial' initial c | ↑f q = inl (q , refl)
  -- noMapsIntoInitial' (↑q q) c with δq q c
  -- noMapsIntoInitial' (↑q q) c | fail = inr refl
  -- noMapsIntoInitial' (↑q q) c | ↑f q' = inl (q' , refl)
