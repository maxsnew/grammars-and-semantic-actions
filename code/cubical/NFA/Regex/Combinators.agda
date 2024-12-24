{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module NFA.Regex.Combinators (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

import      Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (init ; rec ; map)
open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet.More
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec)

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet as Ind
open import Grammar.Inductive.LiftFunctor Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.RegularExpression Alphabet
open import Grammar.Lift.Properties Alphabet

open import NFA.Base Alphabet

open import Helper
open import Term Alphabet

open StrongEquivalence

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFA

-- This file constructs NFAs that are strongly equivalent to
-- regular expressions.
--
-- For each constructor of a regular expression, we build
-- a corresponding NFA. And then we inductively combine smaller
-- NFAs into one machine that is equivalent to the regex

-- Literal
-- Accepts only a single character c, drawn from alphabet Σ₀
module _ (c : ⟨ Alphabet ⟩) where
  -- an NFA with two states,
  -- one transition between them labeled with the character c,
  -- the source of the transition is the initial state,
  -- and the target of this transition is accepting
  data STATE : Type ℓ-zero where
    c-st ε-st : STATE
  open Iso
  STATE≅Fin2 : Iso STATE (Fin 2)
  STATE≅Fin2 .Iso.fun c-st = fzero
  STATE≅Fin2 .Iso.fun ε-st = inr fzero
  STATE≅Fin2 .Iso.inv fzero = c-st
  STATE≅Fin2 .Iso.inv (inr x) = ε-st
  STATE≅Fin2 .Iso.rightInv fzero = refl
  STATE≅Fin2 .Iso.rightInv (inr fzero) = refl
  STATE≅Fin2 .Iso.leftInv c-st = refl
  STATE≅Fin2 .Iso.leftInv ε-st = refl

  isSetSTATE : isSet STATE
  isSetSTATE = isSetRetract (STATE≅Fin2 .fun) (STATE≅Fin2 .inv)
    (STATE≅Fin2 .leftInv)
    isSetFin

  isDiscSTATE : Discrete STATE
  isDiscSTATE = isoPresDiscrete (invIso STATE≅Fin2) discreteFin

  literalNFA : NFA ℓ-zero
  literalNFA .Q = STATE , 2 , ∣ isoToEquiv STATE≅Fin2 ∣₁
  literalNFA .init = c-st
  literalNFA .isAcc c-st = false
  literalNFA .isAcc ε-st = true
  literalNFA .transition = Unit , isFinSetUnit
  literalNFA .src _ = c-st
  literalNFA .dst _ = ε-st
  literalNFA .label _ = c
  literalNFA .ε-transition = Empty.⊥ , isFinSet⊥

  litNFA≅ : StrongEquivalence (Trace literalNFA c-st) (literal c)
  litNFA≅ =
    mkStrEq
      (rec (TraceTy literalNFA) litAlg c-st)
      (toNFA c-st)
      the-ret
      (the-sections c-st)
    where
    ⟦_⟧st : ⟨ literalNFA .Q ⟩ → Grammar ℓ-zero
    ⟦ c-st ⟧st = literal c
    ⟦ ε-st ⟧st = ε

    litAlg : Algebra (TraceTy literalNFA) ⟦_⟧st
    litAlg c-st = ⊕ᴰ-elim (λ { (step t _) →
      ⊗-unit-r ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      })
    litAlg ε-st = ⊕ᴰ-elim (λ { (stop _) → lowerG ∘g lowerG })

    fromNFA = rec (TraceTy literalNFA) litAlg

    toNFA : ∀ q → ⟦ q ⟧st ⊢ Trace literalNFA q
    toNFA c-st = STEP literalNFA _ ∘g id ,⊗ STOP literalNFA Eq.refl ∘g ⊗-unit-r⁻
    toNFA ε-st = STOP literalNFA Eq.refl

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻
      the-ret : rec (TraceTy literalNFA) litAlg c-st ∘g toNFA c-st ≡ id
      the-ret = ⊗-unit-r⁻r

      the-sections :
        ∀ q → toNFA q ∘g fromNFA q ≡ id
      the-sections = equalizer-ind (TraceTy literalNFA) (Trace literalNFA)
                      (λ q → toNFA q ∘g fromNFA q) (λ q → id)
       λ { c-st → ⊕ᴰ≡ _ _ λ { (step tt Eq.refl) →
           (λ i → STEP literalNFA tt ∘g id ,⊗ toNFA ε-st
            ∘g ⊗-unit-rr⁻ i
            ∘g id ,⊗ fromNFA ε-st
            ∘g (lowerG ∘g lowerG) ,⊗ (eq-π (toNFA _ ∘g fromNFA _) id ∘g lowerG))
           ∙ (λ i → STEP literalNFA tt
            ∘g id ,⊗ (eq-π-pf (toNFA _ ∘g fromNFA _) id i)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG)
         }
         ; ε-st → ⊕ᴰ≡ _ _ λ { (stop Eq.refl) → refl } }

-- Nullary Disjunction
module _ where
  ⊥NFA : NFA ℓ-zero
  ⊥NFA .Q = Unit , isFinSetUnit
  ⊥NFA .init = tt
  ⊥NFA .isAcc _ = false
  ⊥NFA .transition = Empty.⊥ , isFinSet⊥
  ⊥NFA .ε-transition = Empty.⊥ , isFinSet⊥

  ⊥NFA≅ : StrongEquivalence (Parse ⊥NFA) ⊥
  ⊥NFA≅ = mkStrEq
    (rec _ ⊥Alg _)
    ⊥-elim
    (⊥-η _ _)
    (equalizer-ind-unit (TraceTy ⊥NFA _)
      (⊕ᴰ≡ _ _ λ { (stop ()) }))
    where
      ⊥Alg : TraceAlg ⊥NFA λ _ → ⊥
      ⊥Alg tt = ⊕ᴰ-elim λ { (stop ()) }

-- Binary Disjunction
-- Given two NFAs N and N', accepts a string if and only if
-- the string is accept by N or by N'
module _ (N : NFA ℓN) (N' : NFA ℓN') where
  data ⊕State : Type (ℓ-max ℓN ℓN') where
    start : ⊕State
    inl   : ⟨ N .Q ⟩  → ⊕State
    inr   : ⟨ N' .Q ⟩ → ⊕State

  ⊕State-rep : ⊕State ≃ (Unit ⊎ (⟨ N .Q ⟩ ⊎ ⟨ N' .Q ⟩))
  ⊕State-rep = isoToEquiv (iso
    (λ { start → inl tt ; (inl x) → inr (inl x) ; (inr x) → inr (inr x) })
    (λ { (inl x) → start ; (inr (inl x)) → inl x ; (inr (inr x)) → inr x })
    (λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl })
    λ { start → refl ; (inl x) → refl ; (inr x) → refl })

  ⊕Trans : FinSet (ℓ-max ℓN ℓN')
  ⊕Trans .fst = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
  ⊕Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊕εTrans : Type (ℓ-max ℓN ℓN') where
    pick-inl : ⊕εTrans
    pick-inr : ⊕εTrans
    N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊕εTrans
    N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊕εTrans

  ⊕εTrans-rep :
    (Unit ⊎ (Unit ⊎ (⟨ N .ε-transition ⟩ ⊎ ⟨ N' .ε-transition ⟩ ))) ≃ ⊕εTrans
  ⊕εTrans-rep = isoToEquiv (iso
    (λ { (inl t) → pick-inl
    ; (inr (inl t)) → pick-inr
    ; (inr (inr (inl t))) → N-ε-trans t
    ; (inr (inr (inr t'))) → N'-ε-trans t' })
    (λ { pick-inl → inl _
    ; pick-inr → inr (inl _)
    ; (N-ε-trans t) → inr (inr (inl t))
    ; (N'-ε-trans t') → inr (inr (inr t')) })
    (λ { pick-inl → refl
    ; pick-inr → refl
    ; (N-ε-trans t) → refl
    ; (N'-ε-trans t') → refl })
    (λ { (inl t) → refl
    ; (inr (inl t)) → refl
    ; (inr (inr (inl t))) → refl
    ; (inr (inr (inr t'))) → refl }))

  ⊕NFA : NFA (ℓ-max ℓN ℓN')
  ⊕NFA .Q = ⊕State , EquivPresIsFinSet (invEquiv ⊕State-rep)
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (N .Q) (N' .Q)))
  ⊕NFA .init = start
  ⊕NFA .isAcc start = false
  ⊕NFA .isAcc (inl q) = N .isAcc q
  ⊕NFA .isAcc (inr q') = N' .isAcc q'
  ⊕NFA .transition = ⊕Trans
  ⊕NFA .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
  ⊕NFA .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
  ⊕NFA .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
  ⊕NFA .ε-transition =
    ⊕εTrans ,
    EquivPresIsFinSet ⊕εTrans-rep
      (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ , isFinSetUnit)
        (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))))
  ⊕NFA .ε-src = λ
    { pick-inl → start ; pick-inr → start
    ; (N-ε-trans t) → inl (N .ε-src t)
    ; (N'-ε-trans t') → inr (N' .ε-src t') }
  ⊕NFA .ε-dst = λ
    { pick-inl → inl (N .init)
    ; pick-inr → inr (N' .init)
    ; (N-ε-trans t) → inl (N .ε-dst t)
    ; (N'-ε-trans t') → inr (N' .ε-dst t')
    }

  ⊕NFA≅ : StrongEquivalence (Parse ⊕NFA) (Parse N ⊕ Parse N')
  ⊕NFA≅ =
    mkStrEq
      (fromNFA start)
      (toNFA start)
      (the-ret start)
      (the-sec start)
    where
    ⟦_⟧⊕ : ⟨ ⊕NFA .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ start ⟧⊕ = Parse N  ⊕ Parse N'
    ⟦ inl q ⟧⊕ = LiftG ℓN' (Trace N q)
    ⟦ inr q' ⟧⊕ = LiftG ℓN (Trace N' q')

    ⊕Alg : Algebra (TraceTy ⊕NFA) ⟦_⟧⊕
    ⊕Alg start =
      ⊕ᴰ-elim (λ {
        (step (inl t) ())
      ; (step (inr t) ())
      ; (stepε pick-inl Eq.refl) → ⊕-inl ∘g lowerG ∘g lowerG
      ; (stepε pick-inr Eq.refl) → ⊕-inr ∘g lowerG ∘g lowerG})
    ⊕Alg (inl q) = ⊕ᴰ-elim λ {
        (stop acc) → liftG ∘g STOP N acc ∘g lowerG ∘g lowerG
      ; (step (inl t) Eq.refl) → liftG ∘g STEP N t ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
      ; (stepε (N-ε-trans t) Eq.refl) → liftG ∘g STEPε N t ∘g lowerG ∘g lowerG }
    ⊕Alg (inr q') =
      ⊕ᴰ-elim (λ {
        (stop acc) → liftG ∘g STOP N' acc ∘g lowerG ∘g lowerG
      ; (step (inr t) Eq.refl) → liftG ∘g STEP N' t ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
      ; (stepε (N'-ε-trans t) Eq.refl) → liftG ∘g STEPε N' t ∘g lowerG ∘g lowerG})

    fromNFA = rec (TraceTy ⊕NFA) ⊕Alg

    ⟦_⟧N : ⟨ N .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q ⟧N = Trace ⊕NFA (inl q)

    ⟦_⟧N' : ⟨ N' .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q' ⟧N' = Trace ⊕NFA (inr q')

    NAlg : Algebra (TraceTy N) ⟦_⟧N
    NAlg q =
      ⊕ᴰ-elim (λ {
        (stop acc) → STOP ⊕NFA acc ∘g lowerG ∘g lowerG
      ; (step t Eq.refl) → STEP ⊕NFA (inl t) ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε t Eq.refl) → STEPε ⊕NFA (N-ε-trans t) ∘g lowerG })

    N→⊕NFA = rec (TraceTy N) NAlg

    N'Alg : Algebra (TraceTy N') ⟦_⟧N'
    N'Alg q' =
      ⊕ᴰ-elim (λ {
        (stop acc) → STOP ⊕NFA acc ∘g lowerG ∘g lowerG
      ; (step t Eq.refl) → STEP ⊕NFA (inr t) ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε t Eq.refl) → STEPε ⊕NFA (N'-ε-trans t) ∘g lowerG })

    N'→⊕NFA = rec (TraceTy N') N'Alg

    toNFA : ∀ q → ⟦ q ⟧⊕ ⊢ Trace ⊕NFA q
    toNFA start =
      ⊕-elim
        (STEPε ⊕NFA pick-inl ∘g N→⊕NFA (N .init))
        (STEPε ⊕NFA pick-inr ∘g N'→⊕NFA (N' .init))
    toNFA (inl q) = N→⊕NFA q ∘g lowerG
    toNFA (inr q') = N'→⊕NFA q' ∘g lowerG

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊕-elim eq-intro
      the-retN : ∀ q → lowerG ∘g fromNFA (inl q) ∘g toNFA (inl q) ∘g liftG ≡ id
      the-retN =
        equalizer-ind (TraceTy N) _ _ _
          λ q → ⊕ᴰ≡ _ _ (λ {
            (stop x) → refl
          ; (step t Eq.refl) → λ i →
              STEP N t ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          ; (stepε t Eq.refl) → λ i →
              STEPε N t ∘g eq-π-pf _ _ i ∘g lowerG })

      the-retN' : ∀ q' → lowerG ∘g fromNFA (inr q') ∘g toNFA (inr q') ∘g liftG ≡ id
      the-retN' =
        equalizer-ind (TraceTy N') _ _ _
          λ q' → ⊕ᴰ≡ _ _ (λ {
            (stop x) → refl
          ; (step t Eq.refl) → λ i →
              STEP N' t ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          ; (stepε t Eq.refl) → λ i →
              STEPε N' t ∘g eq-π-pf _ _ i ∘g lowerG })

      the-ret : ∀ q → fromNFA q ∘g toNFA q  ≡ id
      the-ret start =
        ⊕≡ _ _
          (λ i → ⊕-inl ∘g the-retN (N .init) i)
          (λ i → ⊕-inr ∘g the-retN' (N' .init) i)
      the-ret (inl q) i = liftG ∘g the-retN q i ∘g lowerG
      the-ret (inr q') i = liftG ∘g the-retN' q' i ∘g lowerG

      the-sec : ∀ q → toNFA q ∘g fromNFA q ≡ id
      the-sec = equalizer-ind _ _ _ _
        λ { start → ⊕ᴰ≡ _ _ (λ {
             (step (inl t) ())
           ; (step (inr t) ())
           ; (stepε pick-inl Eq.refl) → λ i →
             STEPε ⊕NFA pick-inl ∘g eq-π-pf _ _ i ∘g lowerG
           ; (stepε pick-inr Eq.refl) → λ i →
             STEPε ⊕NFA pick-inr ∘g eq-π-pf _ _ i ∘g lowerG})
         ; (inl q) → ⊕ᴰ≡ _ _ λ {
             (stop x) → refl
           ; (step (inl t) Eq.refl) → λ i →
             STEP ⊕NFA (inl t) ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
           ; (stepε (N-ε-trans t) Eq.refl) → λ i →
             STEPε ⊕NFA (N-ε-trans t) ∘g eq-π-pf _ _ i ∘g lowerG }
         ; (inr q') → ⊕ᴰ≡ _ _ λ {
             (stop x) → refl
           ; (step (inr t) Eq.refl) → λ i →
             STEP ⊕NFA (inr t) ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
           ; (stepε (N'-ε-trans t) Eq.refl) → λ i →
             STEPε ⊕NFA (N'-ε-trans t) ∘g eq-π-pf _ _ i ∘g lowerG }}

-- Epsilon, the nullary sequencing
module _ where
  -- an NFA with one state,
  -- no transitions,
  -- and the single state is both initial and accepting
  εNFA : NFA ℓ-zero
  εNFA .Q = Unit , isFinSetUnit
  εNFA .init = tt
  εNFA .isAcc _ = true
  εNFA .transition = Empty.⊥ , isFinSet⊥
  εNFA .ε-transition = Empty.⊥ , isFinSet⊥

  εNFA≅ : StrongEquivalence (Parse εNFA) ε
  εNFA≅ = mkStrEq
    (rec _ εAlg _)
    (STOP εNFA Eq.refl)
    refl
    (equalizer-ind-unit (TraceTy εNFA _) (⊕ᴰ≡ _ _ (λ { (stop Eq.refl) → refl })))
    where
      εAlg : TraceAlg εNFA λ _ → ε
      εAlg tt = ⊕ᴰ-elim (λ { (stop Eq.refl) → lowerG ∘g lowerG})

-- Concatenation
-- Given two NFAs N and N', accepts a string w if and only if
-- w ≡ w₁ ++ w₂ where w₁ is accepted by N and w₂ accepted by N'
module _ (N : NFA ℓN) (N' : NFA ℓN') where
  ⊗State : FinSet (ℓ-max ℓN ℓN')
  ⊗State .fst = ⟨ N .Q ⟩ ⊎ ⟨ N' .Q ⟩
  ⊗State .snd = isFinSet⊎ (N .Q) (N' .Q)

  ⊗Trans : FinSet (ℓ-max ℓN ℓN')
  ⊗Trans .fst = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
  ⊗Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊗εTrans : Type (ℓ-max ℓN ℓN') where
    N-acc : ∀ q → (true Eq.≡ N .isAcc q) → ⊗εTrans
    N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊗εTrans
    N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊗εTrans

  ⊗εTrans-rep :
    (Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q)) ⊎
      (⟨ N .ε-transition ⟩ ⊎ ⟨ N' .ε-transition ⟩)
      ≃ ⊗εTrans
  ⊗εTrans-rep = isoToEquiv (iso
    (λ { (inl (acc)) → N-acc _ (acc .snd)
       ; (inr (inl t)) → N-ε-trans t
       ; (inr (inr t')) → N'-ε-trans t'})
    (λ { (N-acc q acc) → inl (q , acc)
       ; (N-ε-trans t) → inr (inl t)
       ; (N'-ε-trans t') → inr (inr t') })
    (λ { (N-acc _ _) → refl
       ; (N-ε-trans _) → refl
       ; (N'-ε-trans _) → refl})
    (λ { (inl _) → refl
       ; (inr (inl _)) → refl
       ; (inr (inr _)) → refl }))

  ⊗NFA : NFA (ℓ-max ℓN ℓN')
  ⊗NFA .Q = ⊗State
  ⊗NFA .init = inl (N .init)
  ⊗NFA .isAcc = λ { (inl q) → false
                  ; (inr q') → N' .isAcc q' }
  ⊗NFA .transition = ⊗Trans
  ⊗NFA .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
  ⊗NFA .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
  ⊗NFA .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
  ⊗NFA .ε-transition .fst = ⊗εTrans
  ⊗NFA .ε-transition .snd =
    EquivPresIsFinSet ⊗εTrans-rep
      (isFinSet⊎
        ((_ , isFinSetΣ (N .Q)
          (λ q → _ , isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd))))
        (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
    where
      the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) (λ P → Dec (P .fst))
      the-dec-prop q =  isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  ⊗NFA .ε-src = λ { (N-acc q qAcc) → inl q
                  ; (N-ε-trans t) → inl (N .ε-src t)
                  ; (N'-ε-trans t') → inr (N' .ε-src t') }
  ⊗NFA .ε-dst = λ { (N-acc q qAcc) → inr (N' .init)
                  ; (N-ε-trans t) → inl (N .ε-dst t)
                  ; (N'-ε-trans t') → inr (N' .ε-dst t') }

  ⊗NFA≅ : StrongEquivalence (Parse ⊗NFA) (Parse N ⊗ Parse N')
  ⊗NFA≅ =
    mkStrEq
      (rec _ ⊗Alg (⊗NFA .init))
      (N→⊗NFA (N .init))
      (the-retN (N .init))
      (the-secN (N .init))
    where
    ⟦_⟧⊗ : ⟨ ⊗NFA .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ inl q ⟧⊗ = Trace N q ⊗ Parse N'
    ⟦ inr q' ⟧⊗ = LiftG ℓN (Trace N' q')

    ⟦_⟧N : ⟨ N .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q ⟧N = Trace ⊗NFA (inl q) ⟜ Trace ⊗NFA (inr (N' .init))

    ⟦_⟧N' : ⟨ N' .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q' ⟧N' = Trace ⊗NFA (inr q')

    ⊗Alg : Algebra (TraceTy ⊗NFA) ⟦_⟧⊗
    ⊗Alg (inl q) = ⊕ᴰ-elim (λ {
        (step (inl t) Eq.refl) →
          (STEP N t ,⊗ id
          ∘g ⊗-assoc)
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε (N-acc q acc) Eq.refl) →
          STOP N acc ,⊗ id
          ∘g ⊗-unit-l⁻
          ∘g lowerG ∘g lowerG
      ; (stepε (N-ε-trans t) Eq.refl) →
         STEPε N t ,⊗ id
         ∘g lowerG })
    ⊗Alg (inr q') = ⊕ᴰ-elim (λ {
        (stop acc) → liftG ∘g STOP N' acc ∘g lowerG ∘g lowerG
      ; (step (inr t) Eq.refl) →
        liftG ∘g STEP N' t
        ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
      ; (stepε (N'-ε-trans t) Eq.refl) →
        liftG ∘g STEPε N' t ∘g lowerG ∘g lowerG})

    N'Alg : Algebra (TraceTy N') ⟦_⟧N'
    N'Alg q =
      ⊕ᴰ-elim λ {
        (stop acc) → STOP ⊗NFA acc ∘g lowerG ∘g lowerG
      ; (step t Eq.refl) → STEP ⊗NFA (inr t) ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε t Eq.refl) → STEPε ⊗NFA (N'-ε-trans t) ∘g lowerG}

    NAlg : Algebra (TraceTy N) ⟦_⟧N
    NAlg q = ⊕ᴰ-elim λ {
         (stop acc) →
           ⟜-intro
             (STEPε ⊗NFA (N-acc q acc)
             ∘g ⊗-unit-l
             ∘g (lowerG ∘g lowerG) ,⊗ id)
       ; (step t Eq.refl) →
           ⟜-intro
             (STEP ⊗NFA (inl t)
             ∘g id ,⊗ ⟜-app
             ∘g ⊗-assoc⁻
             ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
       ; (stepε t Eq.refl) →
           ⟜-intro
             (STEPε ⊗NFA (N-ε-trans t)
             ∘g ⟜-app
             ∘g lowerG ,⊗ id)
       }

    N→⊗NFA : ∀ q → Trace N q ⊗ Parse N' ⊢ Trace ⊗NFA (inl q)
    N→⊗NFA q =
      ⟜-intro⁻ (rec (TraceTy N) NAlg q)
      ∘g id ,⊗ rec _ N'Alg (N' .init)

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊕-elim eq-intro
      the-retN' : ∀ q' →
        lowerG ∘g rec _ ⊗Alg (inr q') ∘g rec _ N'Alg q' ≡ id
      the-retN' =
        equalizer-ind (TraceTy N') _ _ _
          (λ q' → ⊕ᴰ≡ _ _ λ {
            (stop acc) → refl
          ; (step t Eq.refl) → λ i →
            STEP N' t
            ∘g id ,⊗ eq-π-pf _ _ i
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          ; (stepε t Eq.refl) → λ i →
            STEPε N' t
            ∘g eq-π-pf _ _ i
            ∘g lowerG
          } )

      the-retN : ∀ q →
        rec _ ⊗Alg (inl q) ∘g N→⊗NFA q ≡ id
      the-retN q =
        isoFunInjective ⟜UMP _ _
        (equalizer-ind (TraceTy N)
          (λ q → (Trace N q ⊗ Parse N') ⟜ Parse N')
          (λ q → ⟜-intro (rec (TraceTy ⊗NFA) ⊗Alg (inl q) ∘g N→⊗NFA q))
          (λ q → ⟜-intro id)
          (λ q → ⊕ᴰ≡ _ _
            λ {
            (stop acc) →
              isoFunInjective (invIso ⟜UMP) _ _
                (⟜-intro⁻
                  (⟜-intro (rec (TraceTy ⊗NFA) ⊗Alg (inl q) ∘g N→⊗NFA q) ∘g
                   STOP N acc ∘g lowerG ∘g lowerG
                   )
                  ≡⟨ (λ i →
                        ⟜-intro⁻
                          (⟜-intro-natural
                            {f = rec _ ⊗Alg (inl q) ∘g N→⊗NFA q}
                            {f' = STOP N acc ∘g lowerG ∘g lowerG}
                            i)) ⟩
                (⟜-intro⁻
                  (⟜-intro
                    (rec (TraceTy ⊗NFA) ⊗Alg (inl q)
                     ∘g N→⊗NFA q
                     ∘g (STOP N acc ∘g lowerG ∘g lowerG) ,⊗ id
                    )
                  )
                )
                  ≡⟨ ⟜-β _ ⟩
                rec (TraceTy ⊗NFA) ⊗Alg (inl q)
                  ∘g ⟜-intro⁻
                      (⟜-intro
                         (STEPε ⊗NFA (N-acc q acc)
                         ∘g ⊗-unit-l
                         ∘g (lowerG ∘g lowerG) ,⊗ id)
                      )
                  ∘g id ,⊗ rec _ N'Alg (N' .init)
                  ≡⟨ (λ i →
                        rec (TraceTy ⊗NFA) ⊗Alg (inl q)
                        ∘g ⟜-β (STEPε ⊗NFA (N-acc q acc)
                                ∘g ⊗-unit-l
                                ∘g (lowerG ∘g lowerG) ,⊗ id) i
                        ∘g id ,⊗ rec _ N'Alg (N' .init)
                        ) ⟩
                STOP N acc ,⊗ id
                ∘g ⊗-unit-l⁻
                ∘g lowerG
                ∘g rec _ ⊗Alg (inr (N' .init))
                ∘g ⊗-unit-l
                ∘g id ,⊗ rec _ N'Alg (N' .init)
                ∘g (lowerG ∘g lowerG) ,⊗ id
                  ≡⟨ (λ i →
                       STOP N acc ,⊗ id
                       ∘g ⊗-unit-l⁻
                       ∘g lowerG
                       ∘g rec _ ⊗Alg (inr (N' .init))
                       ∘g ⊗-unit-l⊗-intro (rec _ N'Alg (N' .init)) (~ i)
                       ∘g (lowerG ∘g lowerG) ,⊗ id
                      ) ⟩
                STOP N acc ,⊗ id
                ∘g ⊗-unit-l⁻
                ∘g lowerG
                ∘g rec _ ⊗Alg (inr (N' .init))
                ∘g rec _ N'Alg (N' .init)
                ∘g ⊗-unit-l
                ∘g (lowerG ∘g lowerG) ,⊗ id
                  ≡⟨ (λ i →
                       STOP N acc ,⊗ id
                       ∘g ⊗-unit-l⁻
                       ∘g the-retN' (N' .init) i
                       ∘g ⊗-unit-l
                       ∘g (lowerG ∘g lowerG) ,⊗ id
                      ) ⟩
                STOP N acc ,⊗ id
                ∘g ⊗-unit-l⁻
                ∘g ⊗-unit-l
                ∘g (lowerG ∘g lowerG) ,⊗ id
                  ≡⟨ (λ i →
                       STOP N acc ,⊗ id
                        ∘g ⊗-unit-ll⁻ i
                        ∘g (lowerG ∘g lowerG) ,⊗ id
                     ) ⟩
                (STOP N acc ∘g lowerG ∘g lowerG) ,⊗ id
                  ≡⟨ sym (⟜-β _) ⟩
                 ⟜-intro⁻
                  (⟜-intro
                    ((STOP N acc ∘g lowerG ∘g lowerG) ,⊗ id))
                  ≡⟨ (λ i →
                        ⟜-intro⁻
                          (⟜-intro-natural
                            {f = id}
                            {f' = STOP N acc ∘g lowerG ∘g lowerG}
                            (~ i))) ⟩
                 ⟜-intro⁻
                  (⟜-intro id ∘g
                   STOP N acc ∘g lowerG ∘g lowerG
                   )
                 ∎)
          ; (step t Eq.refl) →
              isoFunInjective (invIso ⟜UMP) _ _
                (⟜-intro⁻
                  (⟜-intro
                      (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .src t))
                         ∘g N→⊗NFA (N .src t))
                  ∘g STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                  )
                  ≡⟨ (λ i →
                        ⟜-intro⁻
                          (⟜-intro-natural
                            {f = rec (TraceTy ⊗NFA) ⊗Alg (inl (N .src t)) ∘g N→⊗NFA (N .src t) }
                            {f' = STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG }
                            i)) ⟩
                ⟜-intro⁻
                  (⟜-intro
                      (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .src t))
                         ∘g N→⊗NFA (N .src t)
                         ∘g (STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG)
                            ,⊗ id)
                  )
                  ≡⟨ ⟜-β _ ⟩
                rec (TraceTy ⊗NFA) ⊗Alg (inl (N .src t))
                ∘g ⟜-intro⁻
                  (⟜-intro
                  (STEP ⊗NFA (inl t)
                  ∘g id ,⊗ ⟜-app
                  ∘g ⊗-assoc⁻
                  ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id))
                ∘g ((liftG ∘g liftG) ,⊗ (liftG ∘g rec (TraceTy N) NAlg (N .dst t))) ,⊗ id
                ∘g (id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                ∘g id ,⊗ rec _ N'Alg (N' .init)
                  ≡⟨
                    (λ i →
                      rec (TraceTy ⊗NFA) ⊗Alg (inl (N .src t))
                      ∘g ⟜-β
                        (STEP ⊗NFA (inl t)
                        ∘g id ,⊗ ⟜-app
                        ∘g ⊗-assoc⁻
                        ∘g ((lowerG ∘g lowerG {ℓ' = ℓ-max ℓN ℓN'}) ,⊗ lowerG {ℓ' = ℓN}) ,⊗ id)
                        i
                      ∘g ((liftG ∘g liftG {ℓ' = ℓN}) ,⊗ (liftG ∘g rec (TraceTy N) NAlg (N .dst t))) ,⊗ id
                      ∘g (id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                      ∘g id ,⊗ rec _ N'Alg (N' .init)
                    )
                  ⟩
                STEP N t ,⊗ id
                ∘g ⊗-assoc
                ∘g id ,⊗ (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t)) ∘g N→⊗NFA (N .dst t))
                ∘g id ,⊗ (eq-π _ _ ,⊗ id)
                ∘g ⊗-assoc⁻
                ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                  ≡⟨
                    (λ i →
                    STEP N t ,⊗ id
                    ∘g ⊗-assoc
                    ∘g id ,⊗ eq-π-pf-⟜-intro (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t)) ∘g N→⊗NFA (N .dst t)) id i
                    ∘g ⊗-assoc⁻
                    ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
                  ⟩
                STEP N t ,⊗ id
                ∘g ⊗-assoc
                ∘g ⊗-assoc⁻
                ∘g (id ,⊗ eq-π _ _) ,⊗ id
                ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                  ≡⟨
                    (λ i →
                       STEP N t ,⊗ id
                       ∘g ⊗-assoc∘⊗-assoc⁻≡id i
                       ∘g (id ,⊗ eq-π _ _) ,⊗ id
                       ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                    )
                  ⟩
                (STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                  ≡⟨ sym (⟜-β _) ⟩
                ⟜-intro⁻
                  (⟜-intro
                     ((STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id))
                  ≡⟨ (λ i →
                        ⟜-intro⁻
                          (⟜-intro-natural
                            {f = id}
                            {f' = STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG }
                            (~ i))) ⟩
                ⟜-intro⁻
                  (⟜-intro id
                     ∘g STEP N t ∘g id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG)
                 ∎)
          ; (stepε t Eq.refl) →
              isoFunInjective (invIso ⟜UMP) _ _
                (
                ⟜-intro⁻
                  (⟜-intro
                      (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-src t)) ∘g
                       N→⊗NFA (N .ε-src t))
                    ∘g STEPε N t ∘g eq-π _ _ ∘g lowerG
                   )
                  ≡⟨
                    (λ i →
                      ⟜-intro⁻
                        (⟜-intro-natural
                          {f = rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-src t)) ∘g N→⊗NFA (N .ε-src t)}
                          {f' = STEPε N t ∘g eq-π _ _ ∘g lowerG}
                          i
                        )
                    )
                  ⟩
                ⟜-intro⁻
                  (⟜-intro
                      (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-src t)) ∘g
                       N→⊗NFA (N .ε-src t)
                      ∘g (STEPε N t ∘g eq-π _ _ ∘g lowerG) ,⊗ id
                   ))
                  ≡⟨ ⟜-β _ ⟩
                rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-src t))
                ∘g
                  ⟜-intro⁻ (⟜-intro
                    (STEPε ⊗NFA (N-ε-trans t)
                    ∘g ⟜-app
                    ∘g lowerG ,⊗ id))
                ∘g (liftG ∘g rec (TraceTy N) NAlg (N .ε-dst t)) ,⊗ id
                ∘g (eq-π _ _ ∘g lowerG) ,⊗ id
                ∘g id ,⊗ rec _ N'Alg (N' .init)
                  ≡⟨
                    (λ i →
                      rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-src t))
                      ∘g ⟜-β
                          (STEPε ⊗NFA (N-ε-trans t)
                            ∘g ⟜-app
                            ∘g lowerG {ℓ' = ℓN} ,⊗ id)
                         i
                      ∘g (liftG ∘g rec (TraceTy N) NAlg (N .ε-dst t)) ,⊗ id
                      ∘g (eq-π _ _ ∘g lowerG) ,⊗ id
                      ∘g id ,⊗ rec _ N'Alg (N' .init)
                    )
                   ⟩
                STEPε N t ,⊗ id
                ∘g rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-dst t))
                ∘g N→⊗NFA (N .ε-dst t)
                ∘g (eq-π _ _ ∘g lowerG) ,⊗ id
                  ≡⟨
                    (λ i →
                      STEPε N t ,⊗ id
                      ∘g eq-π-pf-⟜-intro (rec (TraceTy ⊗NFA) ⊗Alg (inl (N .ε-dst t)) ∘g N→⊗NFA (N .ε-dst t)) id i
                      ∘g lowerG ,⊗ id
                    )
                  ⟩
                (STEPε N t ∘g eq-π _ _ ∘g lowerG) ,⊗ id
                  ≡⟨ sym (⟜-β _) ⟩
                ⟜-intro⁻ (⟜-intro ((STEPε N t ∘g eq-π _ _ ∘g lowerG) ,⊗ id))
                  ≡⟨
                    (λ i →
                      ⟜-intro⁻
                        (⟜-intro-natural
                          {f = id}
                          {f' = STEPε N t ∘g eq-π _ _ ∘g lowerG}
                          (~ i)
                        )
                    )
                  ⟩
                ⟜-intro⁻ (⟜-intro id ∘g STEPε N t ∘g eq-π _ _ ∘g lowerG)
                 ∎)
              })
          q)

      -- Annoying artifact of how equalizer-induction is written:
      -- Need to handle each of the ⊗NFA states, even if the inl
      -- half of this proof is unecessary
      -- To handle this, map the inl terms to ⊤* so the
      -- equations are trivial to prove
      the-secN' : ∀ q' →
        rec _ N'Alg q' ∘g lowerG ∘g rec _ ⊗Alg (inr q') ≡ id
      the-secN' q' =
        equalizer-ind
          (TraceTy ⊗NFA)
          (λ {
            (inl q) → ⊤*
          ; (inr q') → Trace ⊗NFA (inr q')})
          (λ {
            (inl q) → ⊤*-intro
          ; (inr q') → rec _ N'Alg q' ∘g lowerG ∘g rec _ ⊗Alg (inr q')})
          (λ {
            (inl q) → ⊤*-intro
          ; (inr q') → id})
          (λ {
            (inl q) → unambiguous⊤* _ _
          ; (inr q') →
              ⊕ᴰ≡ _ _ λ {
                  (stop acc) → refl
              ; (step (inr t) Eq.refl) → λ i →
                  STEP ⊗NFA (inr t) ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
              ; (stepε (N'-ε-trans t) Eq.refl) → λ i →
                  STEPε ⊗NFA (N'-ε-trans t) ∘g eq-π-pf _ _ i ∘g lowerG
              }
          })
          (inr q')

      the-secN : ∀ q →
        N→⊗NFA q ∘g rec _ ⊗Alg (inl q) ≡ id
      the-secN q =
        equalizer-ind
          (TraceTy ⊗NFA)
          (λ {
            (inl q) → Trace ⊗NFA (inl q)
          ; (inr q') → ⊤*
          })
          (λ {
            (inl q) → N→⊗NFA q ∘g rec _ ⊗Alg (inl q)
          ; (inr q') → ⊤*-intro
          })
          (λ {
            (inl q) → id
          ; (inr q') → ⊤*-intro
          })
          (λ {
            (inl q) →
              ⊕ᴰ≡ _ _
                λ {
                  (step (inl t) Eq.refl) →
                    (
                    ⟜-intro⁻ (⟜-intro
                        (STEP ⊗NFA (inl t)
                        ∘g id ,⊗ ⟜-app
                        ∘g ⊗-assoc⁻
                        ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id))
                    ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
                    ∘g (id ,⊗ rec (TraceTy N) NAlg (N .dst t)) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g ⊗-assoc
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                          ⟜-β
                            (STEP ⊗NFA (inl t)
                              ∘g id ,⊗ ⟜-app
                              ∘g ⊗-assoc⁻
                              ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id) i
                          ∘g ((liftG {ℓ' = ℓ-max ℓN ℓN'}
                                ∘g liftG {ℓ' = ℓN}) ,⊗ liftG {ℓ' = ℓN}) ,⊗ id
                          ∘g (id ,⊗ rec (TraceTy N) NAlg (N .dst t)) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g ⊗-assoc
                          ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t))
                          ∘g id ,⊗ eq-π _ _
                          ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                        )
                      ⟩
                    STEP ⊗NFA (inl t)
                    ∘g id ,⊗ ⟜-app
                    ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                    ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                    ∘g ⊗-assoc⁻
                    ∘g ⊗-assoc
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                         STEP ⊗NFA (inl t)
                         ∘g id ,⊗ ⟜-app
                         ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                         ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                         ∘g ⊗-assoc⁻∘⊗-assoc≡id i
                         ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t))
                         ∘g id ,⊗ eq-π _ _
                         ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                         )
                      ⟩
                    STEP ⊗NFA (inl t)
                    ∘g id ,⊗ ⟜-app
                    ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                    ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                          STEP ⊗NFA (inl t)
                          ∘g id ,⊗ eq-π-pf _ _ i
                          ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                         )
                      ⟩
                    STEP ⊗NFA (inl t)
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                    ∎
                    )
                ; (stepε (N-ε-trans t) Eq.refl) →
                    (
                    ⟜-intro⁻ (⟜-intro
                         (STEPε ⊗NFA (N-ε-trans t)
                         ∘g ⟜-app
                         ∘g lowerG ,⊗ id))
                    ∘g liftG ,⊗ id
                    ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g rec _ ⊗Alg (inl (N .ε-dst t))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          ⟜-β
                            (STEPε ⊗NFA (N-ε-trans t)
                            ∘g ⟜-app
                            ∘g lowerG {ℓ' = ℓN} ,⊗ id)
                            i
                          ∘g liftG ,⊗ id
                          ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g rec _ ⊗Alg (inl (N .ε-dst t))
                          ∘g eq-π _ _
                          ∘g lowerG
                          )
                      ⟩
                    STEPε ⊗NFA (N-ε-trans t)
                    ∘g ⟜-app
                    ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g rec _ ⊗Alg (inl (N .ε-dst t))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨  (λ i →
                          STEPε ⊗NFA (N-ε-trans t)
                          ∘g eq-π-pf _ _ i
                          ∘g lowerG
                          )
                      ⟩
                    STEPε ⊗NFA (N-ε-trans t)
                    ∘g eq-π _ _
                    ∘g lowerG
                    ∎
                    )
                ; (stepε (N-acc q acc) Eq.refl) →
                    (
                    ⟜-app
                    ∘g ⟜-intro
                        (STEPε ⊗NFA (N-acc q acc)
                        ∘g ⊗-unit-l
                        ∘g (lowerG ∘g lowerG) ,⊗ id) ,⊗ id
                    ∘g (liftG ∘g liftG) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g ⊗-unit-l⁻
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          ⟜-β
                          (STEPε ⊗NFA (N-acc q acc)
                            ∘g ⊗-unit-l
                            ∘g (lowerG {ℓ' = ℓN}
                                  ∘g lowerG {ℓ' = ℓ-max ℓN ℓN'}) ,⊗ id) i
                          ∘g (liftG ∘g liftG) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g ⊗-unit-l⁻
                          ∘g lowerG
                          ∘g rec _ ⊗Alg (inr (N' .init))
                          ∘g eq-π _ _
                          ∘g lowerG
                        )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g ⊗-unit-l
                    ∘g ⊗-unit-l⁻
                    ∘g rec _ N'Alg (N' .init)
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          STEPε ⊗NFA (N-acc q acc)
                          ∘g ⊗-unit-l⁻l i
                          ∘g rec _ N'Alg (N' .init)
                          ∘g lowerG
                          ∘g rec _ ⊗Alg (inr (N' .init))
                          ∘g eq-π _ _
                          ∘g lowerG
                         )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g rec _ N'Alg (N' .init)
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨
                        (λ i →
                          STEPε ⊗NFA (N-acc q acc)
                          ∘g the-secN' (N' .init) i
                          ∘g eq-π _ _
                          ∘g lowerG
                        )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g eq-π _ _
                    ∘g lowerG
                    ∎
                    )
                }
          ; (inr q') → unambiguous⊤* _ _
          })
          (inl q)


-- Kleene Star
module _ (N : NFA ℓN) where
  data *εTrans : Type ℓN where
    inr : *εTrans
    cons⟨N⟩ : ∀ {q} → true Eq.≡ N .isAcc q  → *εTrans
    N-internal : ⟨ N .ε-transition ⟩ → *εTrans

  *εTrans-rep :
    (Unit ⊎ ((Σ[ q ∈ _ ] (true Eq.≡ N .isAcc q)) ⊎ ⟨ N .ε-transition ⟩)) ≃ *εTrans
  *εTrans-rep = isoToEquiv
    (iso
      (λ { (inl x) → inr
         ; (inr (inl x)) → cons⟨N⟩ (x .snd)
         ; (inr (inr x)) → N-internal x })
      (λ { inr → inl tt
         ; (cons⟨N⟩ x) → inr (inl (_ , x))
         ; (N-internal x) → inr (inr x)})
      (λ { inr → refl ; (cons⟨N⟩ x) → refl ; (N-internal x) → refl })
      λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl })

  *NFA : NFA ℓN
  *NFA .Q = Unit ⊎ N .Q .fst , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
  *NFA .init = inl _
  *NFA .isAcc (inl _) = true
  *NFA .isAcc (inr q) = false
  *NFA .transition = N .transition
  *NFA .src = inr ∘ N .src
  *NFA .dst = inr ∘ N .dst
  *NFA .label = N .label
  *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ ,
      isFinSetΣ (N .Q) (λ q → _ ,
       isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd)
       )) (N .ε-transition)))
    where
      the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) (λ P → Dec (P .fst))
      the-dec-prop q =  isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  *NFA .ε-src inr = inl _
  *NFA .ε-dst inr = inr (N .init)
  *NFA .ε-src (cons⟨N⟩ {q} _) = inr q
  *NFA .ε-dst (cons⟨N⟩ {q} _) = inl _
  *NFA .ε-src (N-internal t) = inr (N .ε-src t)
  *NFA .ε-dst (N-internal t) = inr (N .ε-dst t)

  *NFA≅ : StrongEquivalence (Parse *NFA) (Parse N *)
  *NFA≅ =
    mkStrEq
      (rec _ *NFAAlg (inl _))
      (rec _ N*Alg _)
      the-ret
      the-sec
    where
    ⟦_⟧* : ⟨ *NFA .Q ⟩ → Grammar ℓN
    ⟦ inl _ ⟧* = Parse N *
    ⟦ inr q ⟧* = Trace N q ⊗ (Parse N *)

    ⟦_⟧N : ⟨ N .Q ⟩ → Grammar ℓN
    ⟦ q ⟧N = Trace *NFA (inr q) ⟜ Trace *NFA (inl _)

    *NFAAlg : Algebra (TraceTy *NFA) ⟦_⟧*
    *NFAAlg (inl _) = ⊕ᴰ-elim (λ {
        (stop Eq.refl) →
          NIL
          ∘g lowerG
          ∘g lowerG
      ; (stepε inr Eq.refl) →
          CONS
          ∘g lowerG
      })
    *NFAAlg (inr q) = ⊕ᴰ-elim (λ {
        (step t Eq.refl) →
          STEP N t ,⊗ id
          ∘g ⊗-assoc
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε (cons⟨N⟩ acc) Eq.refl) →
          STOP N acc ,⊗ id
          ∘g ⊗-unit-l⁻
          ∘g lowerG
      ; (stepε (N-internal t) Eq.refl) →
          STEPε N t ,⊗ id
          ∘g lowerG
      })

    NAlg : Algebra (TraceTy N) ⟦_⟧N
    NAlg q = ⊕ᴰ-elim (λ {
        (stop acc) →
          ⟜-intro
            (STEPε *NFA (cons⟨N⟩ acc)
            ∘g ⊗-unit-l
            ∘g (lowerG ∘g lowerG) ,⊗ id)
      ; (step t Eq.refl) →
         ⟜-intro
           (STEP *NFA t
           ∘g id ,⊗ ⟜-app
           ∘g ⊗-assoc⁻
           ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
      ; (stepε t Eq.refl) →
         ⟜-intro
           (STEPε *NFA (N-internal t)
           ∘g ⟜-app
           ∘g lowerG ,⊗ id
           )
      })

    N*Alg : Algebra (*Ty (Parse N)) (λ _ → Parse *NFA)
    N*Alg _ = ⊕ᴰ-elim (λ {
        nil →
          STOP *NFA Eq.refl
          ∘g lowerG ∘g lowerG
      ; cons →
          STEPε *NFA inr
          ∘g ⟜-app
          ∘g rec _ NAlg (N .init) ,⊗ id
          ∘g lowerG ,⊗ lowerG
      })

    N→*NFA : ∀ q → Trace N q ⊗ (Parse N *) ⊢ Trace *NFA (inr q)
    N→*NFA q =
      ⟜-intro⁻ (rec _ NAlg q)
      ∘g id ,⊗ rec _ N*Alg _

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊕-elim eq-intro LiftDom⊗Iso
      nested-induction-lemma :
        ∀ q →
        rec _ *NFAAlg (inr q)
        ∘g N→*NFA q
        ∘g id ,⊗ rec (TraceTy *NFA) *NFAAlg (inl _)
        ≡
        id ,⊗ rec _ *NFAAlg (inl _)
      nested-induction-lemma = {!!}

      the-ret :
        rec (TraceTy *NFA) *NFAAlg _
        ∘g rec (*Ty (Parse N)) N*Alg _
        ≡
        id
      the-ret =
        equalizer-ind (*Ty (Parse N)) _ _ _
          (λ _ → ⊕ᴰ≡ _ _ λ {
            nil → refl
          ; cons →
            CONS
            ∘g rec _ *NFAAlg (inr (N .init))
            ∘g ⟜-app
            ∘g rec _ NAlg (N .init) ,⊗ id
            ∘g id ,⊗ rec _ N*Alg _
            ∘g lowerG ,⊗ (eq-π _ _ ∘g lowerG)
              ≡⟨
                (λ i →
                  CONS
                  ∘g {!!}
                  ∘g lowerG ,⊗ (eq-π _ _ ∘g lowerG)
                )
              ⟩
            CONS
            ∘g lowerG ,⊗ (eq-π _ _ ∘g lowerG)
            ∎
          })
          _

      the-secN : ∀ q →
        N→*NFA q ∘g rec (TraceTy *NFA) *NFAAlg (inr q) ≡ id
      the-secN q =
        equalizer-ind
          (TraceTy *NFA)
          (λ {
            (inl _) → Parse *NFA
          ; (inr q) → Trace *NFA (inr q)
             }
          )
          (λ {
            (inl _) → id
          ; (inr q) → N→*NFA q ∘g rec _ *NFAAlg (inr q)
             }
          )
          (λ {
            (inl _) → id
          ; (inr q) → id
             }
          )
          (λ {
            (inl _) → refl
          ; (inr q) → ⊕ᴰ≡ _ _ λ {
              (step t Eq.refl) →
                ⟜-intro⁻
                  (⟜-intro
                    (STEP *NFA t
                    ∘g id ,⊗ ⟜-app
                    ∘g ⊗-assoc⁻
                    ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id))
                ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
                ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
                ∘g id ,⊗ rec _ N*Alg _
                ∘g ⊗-assoc
                ∘g id ,⊗ rec _ *NFAAlg (inr (N .dst t))
                ∘g (lowerG ∘g lowerG) ,⊗ (eq-π _ _ ∘g lowerG)
                  ≡⟨
                     (λ i →
                     ⟜-β
                       (STEP *NFA t
                       ∘g id ,⊗ ⟜-app
                       ∘g ⊗-assoc⁻
                       ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
                       i
                     ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
                     ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
                     ∘g id ,⊗ rec _ N*Alg _
                     ∘g ⊗-assoc
                     ∘g id ,⊗ rec _ *NFAAlg (inr (N .dst t))
                     ∘g (lowerG ∘g lowerG) ,⊗ (eq-π _ _ ∘g lowerG)
                     )
                  ⟩
                STEP *NFA t
                ∘g id ,⊗ ⟜-app
                ∘g id ,⊗ (rec _ NAlg (N .dst t) ,⊗ id)
                ∘g ⊗-assoc⁻
                ∘g id ,⊗ rec _ N*Alg _
                ∘g ⊗-assoc
                ∘g id ,⊗ rec _ *NFAAlg (inr (N .dst t))
                ∘g (lowerG ∘g lowerG) ,⊗ (eq-π _ _ ∘g lowerG)
                  ≡⟨ {!!} ⟩
                STEP *NFA t
                ∘g id ,⊗ ⟜-app
                ∘g id ,⊗ (rec _ NAlg (N .dst t) ,⊗ id)
                ∘g id ,⊗ (id ,⊗ rec _ N*Alg _)
                ∘g id ,⊗ rec _ *NFAAlg (inr (N .dst t))
                ∘g (lowerG ∘g lowerG) ,⊗ (eq-π _ _ ∘g lowerG)
                  ≡⟨ {!!} ⟩
                STEP *NFA t
                ∘g (lowerG ∘g lowerG) ,⊗ (eq-π _ _ ∘g lowerG)
                ∎
            ; (stepε (cons⟨N⟩ t) Eq.refl) → {!!}
            ; (stepε (N-internal t) Eq.refl) → {!!}
          }
             }
          )
          (inr q)

      the-sec :
        rec (*Ty (Parse N)) N*Alg _ ∘g rec (TraceTy *NFA) *NFAAlg _ ≡ id
      the-sec =
        equalizer-ind (TraceTy *NFA)
          (λ {
            (inl _) → Parse *NFA
          ; (inr q) → Trace *NFA (inr q)
             }
          )
          (λ {
            (inl _) → rec _ N*Alg _ ∘g rec _ *NFAAlg _
          ; (inr q) → id
             }
          )
          (λ {
            (inl _) → id
          ; (inr q) → id
             }
          )
          (λ {
            (inl _) → ⊕ᴰ≡ _ _
              λ {
                (stop Eq.refl) → refl
              ; (stepε inr Eq.refl) →
                  STEPε *NFA inr
                  ∘g ⟜-app
                  ∘g rec _ NAlg (N .init) ,⊗ id
                  ∘g id ,⊗ rec _ N*Alg _
                  ∘g rec (TraceTy *NFA) *NFAAlg (inr (N .init))
                  ∘g eq-π _ _
                  ∘g lowerG
                    ≡⟨ (λ i →
                        STEPε *NFA inr
                        ∘g the-secN (N .init) i
                        ∘g eq-π _ _
                        ∘g lowerG
                      )
                    ⟩
                  STEPε *NFA inr
                  ∘g eq-π _ _
                  ∘g lowerG
                  ∎
              }
          ; (inr q) → refl
             }
          )
          (*NFA .init)

  -- opaque
  --   unfolding ⊗-unit-l⁻ ⊗-unit-l *r-initial KL*r-elim id*r-AlgebraHom AlgebraHom-seq ∃AlgebraHom recTrace P-initial !PAlgebraHom' P-idAlgebraHom
  --   *-strong-equivalence :
  --     StrongEquivalence (InitParse *NFA) (KL* (InitParse N))
  --   *-strong-equivalence = mkStrEq
  --     (recInit *NFA *Alg)
  --     (foldKL*r (InitParse N) the-KL*-alg)
  --     (!*r-AlgebraHom (InitParse N) (*r-initial (InitParse N))
  --       (record { f = recInit *NFA *Alg ∘g foldKL*r (InitParse N) the-KL*-alg
  --               ; on-nil = refl
  --               ; on-cons = (λ i → KL*.cons ∘g
  --                 nested-induction-lemma i ∘g ⊗-intro id (foldKL*r _ the-KL*-alg))
  --       })
  --       (id*r-AlgebraHom _ _))
  --     (algebra-η *NFA (AlgebraHom-seq _ (∃AlgebraHom _ *Alg)
  --       (record { f = λ {
  --                   (inl _) → foldKL*r _ the-KL*-alg
  --                 ; (inr q) → P-recTrace' _ _ NPAlg ∘g
  --                             ⊗-intro id (foldKL*r _ the-KL*-alg) }
  --               ; on-nil = λ { {inl _} acc → refl }
  --               ; on-cons = λ { t → λ i → cons t ∘g ⊗-intro id
  --              (P-recTrace' N (InitParse *NFA) NPAlg ∘g
  --                ⊗-intro id (foldKL*r (InitParse N) the-KL*-alg))
  --                ∘g ⊗-assoc⁻∘⊗-assoc≡id i }
  --               ; on-ε-cons = λ {
  --                   inr → refl
  --                 ; (cons⟨N⟩ x) →
  --                   λ i → ε-cons (cons⟨N⟩ x) ∘g
  --                     ⊗-unit-l⁻l i ∘g foldKL*r (InitParse N) the-KL*-alg
  --                 ; (N-internal x) → refl } })))
  --     where
  --       *Alg : Algebra *NFA
  --       *Alg .the-ℓs (inl _) = _
  --       *Alg .the-ℓs (inr q) = _
  --       *Alg .G (inl _) = KL* (InitParse N)
  --       *Alg .G (inr q) = Parse N q ⊗ KL* (InitParse N)
  --       *Alg .nil-case {q = inl x} _ = KL*.nil
  --       *Alg .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
  --       *Alg .ε-cons-case inr = KL*.cons
  --       *Alg .ε-cons-case (cons⟨N⟩ acc) = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
  --       *Alg .ε-cons-case (N-internal t) = ⊗-intro (ε-cons t) id

  --       -- given a parse starting at q in N and a *NFA parse, make a
  --       -- *NFA parse starting at q.
  --       NPAlg : PAlgebra N (InitParse *NFA)
  --       NPAlg .the-ℓs = _
  --       NPAlg .G q = Parse *NFA (inr q)
  --       NPAlg .nil-case acc = ε-cons (cons⟨N⟩ acc)
  --       NPAlg .cons-case t = cons t
  --       NPAlg .ε-cons-case t = ε-cons (N-internal t)

  --       open *r-Algebra
  --       -- NOTE : this is not an algebra for NFAs, rather for Kleene star
  --       -- and is used to prove the uniqueness of the foldKL*r term
  --       the-KL*-alg : *r-Algebra (InitParse N)
  --       the-KL*-alg .the-ℓ = _
  --       the-KL*-alg .G = InitParse *NFA
  --       the-KL*-alg .nil-case = nil _
  --       the-KL*-alg .cons-case = ε-cons inr ∘g P-recInit' _ _ NPAlg

  --       NPAlg' : PAlgebra N (InitParse *NFA)
  --       NPAlg' .the-ℓs = _
  --       NPAlg' .G q = Parse N q ⊗ KL* (InitParse N)
  --       NPAlg' .nil-case acc = ⊗-intro (nil acc) (recInit _ *Alg) ∘g ⊗-unit-l⁻
  --       NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
  --       NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

  --       nested-induction-lemma :
  --         Path (InitParse N ⊗ InitParse *NFA ⊢ InitParse N ⊗ KL* (InitParse N))
  --           (recTrace *NFA *Alg ∘g P-recInit' _ _ NPAlg)
  --           (⊗-intro id (recInit *NFA *Alg))
  --       nested-induction-lemma =
  --         !PAlgebraHom' _ _ NPAlg'
  --           rec*Alg∘recInitNPAlgHom
  --           recInit*AlgHom
  --           _
  --         where
  --           rec*Alg∘recInitNPAlgHom : PAlgebraHom N (InitParse *NFA)
  --             (P-initial N (InitParse *NFA))
  --             NPAlg'
  --           rec*Alg∘recInitNPAlgHom .f q =
  --             recTrace *NFA *Alg ∘g P-recTrace' _ _ NPAlg
  --           rec*Alg∘recInitNPAlgHom .on-nil acc =
  --             λ i → ⊗-intro (nil acc) (recInit *NFA *Alg) ∘g
  --               ⊗-unit-ll⁻ i ∘g ⊗-unit-l⁻
  --           rec*Alg∘recInitNPAlgHom .on-cons t =
  --             λ i → (⊗-intro (cons t) id ∘g ⊗-assoc) ∘g
  --               ⊗-intro id (recTrace *NFA *Alg ∘g
  --                 P-recTrace' N (InitParse *NFA) NPAlg) ∘g ⊗-assoc⁻∘⊗-assoc≡id i
  --           rec*Alg∘recInitNPAlgHom .on-ε-cons t = refl

  --           recInit*AlgHom :
  --             PAlgebraHom N
  --               (InitParse *NFA) (P-initial N (InitParse *NFA)) NPAlg'
  --           recInit*AlgHom .f q = ⊗-intro id (recTrace _ *Alg)
  --           recInit*AlgHom .on-nil acc = refl
  --           recInit*AlgHom .on-cons t = refl
  --           recInit*AlgHom .on-ε-cons t = refl
