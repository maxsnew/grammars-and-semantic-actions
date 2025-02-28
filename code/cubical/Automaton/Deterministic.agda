open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automaton.Deterministic (Alphabet : hSet ℓ-zero) where

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
open import Term Alphabet
open import Helper

private
  variable
    ℓ ℓA : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop step : Tag

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → ⊗e (k (literal* c)) (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

  STOP : ∀ {q} → ε ⊢ Trace (isAcc q) q
  STOP =
    roll
    ∘g ⊕ᴰ-in stop
    ∘g ⊕ᴰ-in (lift (Eq.refl))
    ∘g liftG ∘g liftG

  STEP :
    ∀ {b : Bool} →
    {q : Q} →
    (c : ⟨ Alphabet ⟩) →
    ＂ c ＂ ⊗ Trace b (δ q c) ⊢ Trace b q
  STEP c = roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG

  Parse : Grammar _
  Parse = Trace true init

  ParseAlg : (Q → Grammar ℓA) → Type (ℓ-max ℓ ℓA)
  ParseAlg A = Algebra (TraceTy true) A

  TraceAlg : (Q → Grammar ℓA) → Bool → Type (ℓ-max ℓ ℓA)
  TraceAlg A b = Algebra (TraceTy b) A


  open StrongEquivalence
  parseAlg : Algebra (*Ty char) λ _ → &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
  parseAlg _ = ⊕ᴰ-elim (λ {
    nil → &ᴰ-in (λ q →
      ⊕ᴰ-in (isAcc q) ∘g
      roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) ∘g
      liftG ∘g liftG ∘g lowerG ∘g lowerG)
    ; cons → &ᴰ-in (λ q → (
      ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun
          ∘g id ,⊗ &ᴰ-π (δ q c))
      ∘g ⊕ᴰ-distL .fun)
      ∘g lowerG ,⊗ lowerG) })

  parse : string ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
  parse = rec (*Ty char) parseAlg _

  parseInit : string ⊢ ⊕[ b ∈ Bool ] Trace b init
  parseInit = &ᴰ-π init ∘g parse

  printAlg : ∀ b → Algebra (TraceTy b) (λ _ → string)
  printAlg b q = ⊕ᴰ-elim λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → NIL ∘g lowerG ∘g lowerG })
    ; step → CONS ∘g ⊕ᴰ-elim (λ { (lift c) → ⊕ᴰ-in c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG }) }

  print : ∀ b → (q : Q) → Trace b q ⊢ string
  print b q = rec (TraceTy b) (printAlg b) q

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q = ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) })
    ; step → ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun ∘g (lowerG ∘g lowerG) ,⊗ lowerG) })

  Trace≅string : (q : Q) → StrongEquivalence (⊕[ b ∈ Bool ] Trace b q) string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = &ᴰ-π q ∘g parse
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = isRetract
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      isRetract : &ᴰ-π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      isRetract = ⊕ᴰ≡ _ _ λ b →
        ind'
          (TraceTy b)
          (⊕ᴰAlg b)
          ((λ q'  → &ᴰ-π q' ∘g parse ∘g print b q') ,
          λ q' → ⊕ᴰ≡ _ _ (λ {
            stop → funExt λ w → funExt λ {
              ((lift Eq.refl) , p) → refl}
          ; step → ⊕ᴰ≡ _ _ (λ { (lift c) → refl })
          }))
          ((λ q' → ⊕ᴰ-in b) ,
          λ q' → ⊕ᴰ≡ _ _ λ {
            stop → funExt (λ w → funExt λ {
              ((lift Eq.refl) , p) → refl})
          ; step → refl })
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b

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

  FreelyAddFail+Initial≅Unit⊎ : Iso (FreelyAddFail+Initial Q) ((Unit ⊎ Unit) ⊎ Q)
  FreelyAddFail+Initial≅Unit⊎ .fun initial = inl (inl _)
  FreelyAddFail+Initial≅Unit⊎ .fun fail = inl (inr _)
  FreelyAddFail+Initial≅Unit⊎ .fun (↑q q) = inr q
  FreelyAddFail+Initial≅Unit⊎ .inv (inl (inl _)) = initial
  FreelyAddFail+Initial≅Unit⊎ .inv (inl (inr _)) = fail
  FreelyAddFail+Initial≅Unit⊎ .inv (inr q) = ↑q q
  FreelyAddFail+Initial≅Unit⊎ .rightInv (inl (inl _)) = refl
  FreelyAddFail+Initial≅Unit⊎ .rightInv (inl (inr _)) = refl
  FreelyAddFail+Initial≅Unit⊎ .rightInv (inr _) = refl
  FreelyAddFail+Initial≅Unit⊎ .leftInv fail = refl
  FreelyAddFail+Initial≅Unit⊎ .leftInv initial = refl
  FreelyAddFail+Initial≅Unit⊎ .leftInv (↑q _) = refl

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

  open DeterministicAutomaton

  Aut : DeterministicAutomaton (FreelyAddFail+Initial Q)
  Aut .init = initial
  Aut .isAcc fail = false
  Aut .isAcc initial = null
  Aut .isAcc (↑q q) = acc q
  Aut .δ fail _ = fail
  Aut .δ initial c = FreelyAddFail→FreelyAddFail+Initial (δᵢ c)
  Aut .δ (↑q q) c = FreelyAddFail→FreelyAddFail+Initial (δq q c)

  AutAlgCarrier :
    (A-init : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    FreelyAddFail+Initial Q →
    Grammar ℓA
  AutAlgCarrier A-init A fail = ⊥*
  AutAlgCarrier A-init A initial = A-init
  AutAlgCarrier A-init A (↑q q) = A q

  AutAlg :
    (A-init : Grammar ℓA) →
    (A : Q → Grammar ℓA) →
    Type (ℓ-max ℓ ℓA)
  AutAlg A-init A = {!ParseAlg Aut ?!}
