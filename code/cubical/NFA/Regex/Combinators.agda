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

open import Grammar Alphabet hiding (KL* ; NIL ; CONS)
open import Grammar.KleeneStar Alphabet
open import Grammar.Inductive.Indexed Alphabet as Ind
open import Grammar.Inductive.LiftFunctor Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.RegularExpression Alphabet

open import NFA.Base Alphabet

open import Helper
open import Term Alphabet

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
  -- ⊗NFA .isAcc = λ { (inl q) → (Empty.⊥* , isProp⊥*) , (no lower)
  --                 ; (inr q') → LiftDecProp'' {ℓN'}{ℓN} (N' .isAcc q')}
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

  open StrongEquivalence


  ⊗NFA≅ : StrongEquivalence (Parse ⊗NFA) (Parse N ⊗ Parse N')
  ⊗NFA≅ =
    mkStrEq
      (rec _ ⊗Alg (⊗NFA .init))
      (N→⊗NFA (N .init))
      -- (Prec _ _ _ NPAlg (N .init))
      -- (⟜-intro⁻
      --   (rec _ (underlyingAlg N (Parse N') _ NPAlg) (lift (N .init))
      --   ∘g liftF ⟨ N .Q ⟩
      --   ))
      (the-retN (N .init))
      -- (isoFunInjective ⟜UMP _ _
      --   (ind'
      --     (TraceTy N)
      --     (LowerAlg'
      --       ⟨ N .Q ⟩
      --       (underlyingAlg N (Parse N')
      --         (λ (lift q) → Trace N q ⊗ Parse N')
      --         NPAlg'))
      --     (recHomo (TraceTy N) {!!})
      --     (recHomo (TraceTy N) {!!})
      --     (N .init)))
      -- (⟜-intro⁻
      --   (rec _ (underlyingAlg N (Parse N') _ NPAlg) (lift (N .init))))
      -- (isoFunInjective ⟜UMP _ _
      --   {!ind' (PAlgTy N ?) NPAlg ? ? ?!})
      -- (ind-id' (TraceTy ⊗NFA)
      --   (compHomo (TraceTy ⊗NFA) _ ⊗Alg (initialAlgebra (TraceTy ⊗NFA))
      --     -- ⊗Alg→initial
      --     {!!}
      --     (recHomo _ ⊗Alg))
      --   (⊗NFA .init))
      -- (rec _ ⊗Alg (⊗NFA .init))
      -- (⊗Alg→initial .fst (⊗NFA .init))
      -- (isoFunInjective ⟜UMP _ _
      --   (ind' (TraceTy N)
      --     NAlg'
      --     the-hom
      --     (
      --     (λ q → ⟜-intro id) ,
      --     (λ q → ⊕ᴰ≡ _ _ λ {
      --         (stop x) → {!!}
      --       ; (step t Eq.refl) → {!!}
      --       ; (stepε t Eq.refl) → {!!} }))
      --     (N .init))
      -- )
      -- (ind-id' (TraceTy ⊗NFA)
      --   (compHomo (TraceTy ⊗NFA) _ ⊗Alg (initialAlgebra (TraceTy ⊗NFA))
      --     {!!}
      --     (recHomo _ ⊗Alg))
      --   (⊗NFA .init))
      {!!}
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
             ∘g id
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

      -- NPAlg : PAlgebra N (Parse N') λ (lift q) → Trace ⊗NFA (inl q)
      -- NPAlg (lift q) = ⊕ᴰ-elim (λ {
      --     (lift (stop acc)) →
      --       STEPε ⊗NFA (N-acc q acc)
      --       ∘g rec _ N'Alg (N' .init)
      --       ∘g lowerG ∘g lowerG
      --   ; (lift (step t Eq.refl)) →
      --      STEP ⊗NFA (inl t)
      --      ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      --   ; (lift (stepε t Eq.refl)) →
      --      STEPε ⊗NFA (N-ε-trans t)
      --      ∘g lowerG
      --   })


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
      the-retN q = isoFunInjective ⟜UMP _ _
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

      the-sec : ∀ q →
        N→⊗NFA q ∘g rec _ ⊗Alg (inl q) ≡ id
      the-sec = ?


--       NPAlg' :
--         PAlgebra N (Parse N') λ (lift q) → Trace N q ⊗ Parse N'
--       NPAlg' (lift q) = ⊕ᴰ-elim (λ {
--           (lift (stop acc)) →
--             STOP N acc ,⊗ id
--             ∘g ⊗-unit-l⁻
--             ∘g lowerG ∘g lowerG
--         ; (lift (step t Eq.refl)) →
--             STEP N t ,⊗ id
--             ∘g ⊗-assoc
--             ∘g (lowerG ∘g lowerG) ,⊗ lowerG
--         ; (lift (stepε t Eq.refl)) →
--            STEPε N t ,⊗ id
--            ∘g lowerG
--         })

--       N'≅⊗NFA⟨inr⟩ :
--         lowerG
--         ∘g rec _ ⊗Alg (inr (N' .init))
--         ∘g rec _ N'Alg (N' .init) ≡ id
--       N'≅⊗NFA⟨inr⟩ =
--         ind-id'
--           (TraceTy N')
--           (compHomo
--             (TraceTy N')
--             (initialAlgebra (TraceTy N'))
--             N'Alg
--             (initialAlgebra (TraceTy N'))
--             ((λ q' → lowerG ∘g rec _ ⊗Alg (inr q')) ,
--              (λ q' → ⊕ᴰ≡ _ _ λ {
--                (stop acc) → refl
--              ; (step t Eq.refl) → refl
--              ; (stepε t Eq.refl) → refl}))
--             (recHomo _ N'Alg))
--           (N' .init)

--       -- NAlg : Algebra (TraceTy N) ⟦_⟧N
--       -- NAlg q =
--       --   ⊕ᴰ-elim λ {
--       --     (stop acc) →
--       --       ⟜-intro (
--       --         STEPε ⊗NFA (N-acc q acc)
--       --         ∘g ⊗-unit-l
--       --         ∘g (lowerG ∘g lowerG) ,⊗ rec _ N'Alg (N' .init))
--       --   ; (step t Eq.refl) →
--       --       ⟜-intro (
--       --         STEP ⊗NFA (inl t)
--       --         ∘g id ,⊗ ⟜-app
--       --         ∘g ⊗-assoc⁻)
--       --       ∘g (lowerG ∘g lowerG) ,⊗ lowerG
--       --   ; (stepε t Eq.refl) →
--       --       ⟜-intro
--       --         (STEPε ⊗NFA (N-ε-trans t) ∘g ⟜-app)
--       --       ∘g lowerG
--       --   }

--       -- NAlg' :
--       --   Algebra
--       --     (TraceTy N)
--       --     (λ q → (Trace N q ⊗ Parse N') ⟜ Parse N')
--       -- NAlg' q =
--       --   ⊕ᴰ-elim λ {
--       --     (stop acc) →
--       --       ⟜-intro (STOP N acc ,⊗ id)
--       --       ∘g lowerG ∘g lowerG
--       --   ; (step t Eq.refl) →
--       --       ⟜-intro
--       --         (STEP N t ,⊗ id
--       --         ∘g ⊗-assoc
--       --         ∘g id ,⊗ ⟜-app
--       --         ∘g ⊗-assoc⁻)
--       --       ∘g (lowerG ∘g lowerG) ,⊗ lowerG
--       --   ; (stepε t Eq.refl) →
--       --       ⟜-intro
--       --         (STEPε N t ,⊗ id
--       --         ∘g ⟜-app)
--       --       ∘g lowerG
--       --   }

--       -- ⊗Alg : Algebra (TraceTy ⊗NFA) ⟦_⟧⊗
--       -- ⊗Alg (inl q) = ⊕ᴰ-elim (λ {
--       --     (step (inl t) Eq.refl) →
--       --       (STEP N t ,⊗ id
--       --       ∘g ⊗-assoc)
--       --       ∘g (lowerG ∘g lowerG) ,⊗ lowerG
--       --   ; (stepε (N-acc q acc) Eq.refl) →
--       --       STOP N acc ,⊗ id
--       --       ∘g ⊗-unit-l⁻
--       --       ∘g lowerG ∘g lowerG
--       --   ; (stepε (N-ε-trans t) Eq.refl) →
--       --      STEPε N t ,⊗ id
--       --      ∘g lowerG })
--       -- ⊗Alg (inr q') = ⊕ᴰ-elim (λ {
--       --     (stop acc) → liftG ∘g STOP N' acc ∘g lowerG ∘g lowerG
--       --   ; (step (inr t) Eq.refl) →
--       --     liftG ∘g STEP N' t
--       --     ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
--       --   ; (stepε (N'-ε-trans t) Eq.refl) →
--       --     liftG ∘g STEPε N' t ∘g lowerG ∘g lowerG})

--       -- ⊗Alg→initial : Homomorphism (TraceTy ⊗NFA)
--       --   ⊗Alg (initialAlgebra (TraceTy ⊗NFA))
--       -- ⊗Alg→initial .fst (inl q) =
--       --   rec _ NPAlg (lift q) ∘g
--       --   {!!}
--       --   -- ⟜-app ∘g {!rec _ NPAlg ?!} ,⊗ id
--       --   -- ⟜-app ∘g rec (TraceTy N) NPAlg q ,⊗ id
--       -- ⊗Alg→initial .fst (inr q') =
--       --   rec (TraceTy N') N'Alg q' ∘g lowerG
--       -- ⊗Alg→initial .snd (inl q) =
--       --   {!!}
--       -- ⊗Alg→initial .snd (inr q') =
--       --   {!!}
--       --   ⊕ᴰ≡ _ _ λ {
--       --     (step (inl t) Eq.refl) →
--       --       (λ i →
--       --       ⟜-β (STEP ⊗NFA (inl t) ∘g id ,⊗ ⟜-app ∘g ⊗-assoc⁻) i
--       --       ∘g (id ,⊗ rec _ NPAlg (N .dst t)) ,⊗ id
--       --       ∘g ⊗-assoc
--       --       ∘g id ,⊗ lowerG
--       --       ∘g (lowerG ∘g lowerG) ,⊗ id
--       --       ) ∙
--       --       (λ i →
--       --         STEP ⊗NFA (inl t)
--       --         ∘g id ,⊗ (⟜-app ∘g rec _ NPAlg (N .dst t) ,⊗ id)
--       --         ∘g ⊗-assoc⁻∘⊗-assoc≡id i
--       --         ∘g (lowerG ∘g lowerG) ,⊗ lowerG )
--       --   ; (stepε (N-acc q acc) Eq.refl) →
--       --       (λ i →
--       --         ⟜-β (
--       --           STEPε ⊗NFA (N-acc q acc)
--       --           ∘g ⊗-unit-l
--       --           ∘g (lowerG {ℓN} ∘g lowerG {ℓ-max ℓN ℓN'}) ,⊗ rec _ N'Alg (N' .init)) i
--       --         ∘g (liftG ∘g liftG) ,⊗ id
--       --         ∘g ⊗-unit-l⁻
--       --         ∘g lowerG ∘g lowerG) ∙
--       --       (STEPε ⊗NFA (N-acc q acc)
--       --          ∘g ⊗-unit-l
--       --          ∘g id ,⊗ rec (λ v → TraceTy N' v) N'Alg (N' .init)
--       --          ∘g ⊗-unit-l⁻
--       --          ∘g lowerG ∘g lowerG
--       --         ≡⟨ (λ i →
--       --              STEPε ⊗NFA (N-acc q acc)
--       --                 ∘g ⊗-unit-l⊗-intro (rec _ N'Alg (N' .init)) (~ i)
--       --                 ∘g ⊗-unit-l⁻
--       --                 ∘g lowerG ∘g lowerG) ⟩
--       --        STEPε ⊗NFA (N-acc q acc)
--       --          ∘g rec (λ v → TraceTy N' v) N'Alg (N' .init)
--       --          ∘g ⊗-unit-l
--       --          ∘g ⊗-unit-l⁻
--       --          ∘g lowerG ∘g lowerG
--       --         ≡⟨ (λ i →
--       --              STEPε ⊗NFA (N-acc q acc)
--       --                 ∘g rec (λ v → TraceTy N' v) N'Alg (N' .init)
--       --                 ∘g ⊗-unit-l⁻l i
--       --                 ∘g lowerG ∘g lowerG) ⟩
--       --        STEPε ⊗NFA (N-acc q acc)
--       --        ∘g rec _ N'Alg (N' .init)
--       --        ∘g lowerG ∘g lowerG
--       --        ∎)
--       --   ; (stepε (N-ε-trans t) Eq.refl) →
--       --     (λ i →
--       --       ⟜-β (STEPε ⊗NFA (N-ε-trans t) ∘g ⟜-app) i
--       --       ∘g rec _ NPAlg (N .ε-dst t) ,⊗ id
--       --       ∘g lowerG)}
--       -- ⊗Alg→initial .snd (inr q') = ⊕ᴰ≡ _ _ λ {
--       --     (stop acc) → refl
--       --   ; (step (inr t) Eq.refl) → refl
--       --   ; (stepε (N'-ε-trans t) Eq.refl) → refl}

--       -- the-hom :
--       --   Homomorphism
--       --     (TraceTy N)
--       --     (initialAlgebra (TraceTy N))
--       --     NAlg'
--       -- the-hom .fst q =
--       --   ⟜-intro (
--       --     rec _ ⊗Alg (inl q)
--       --     ∘g ⟜-app
--       --     ∘g rec _ NAlg q ,⊗ id)
--       -- the-hom .snd q =
--       --   ⊕ᴰ≡ _ _ λ {
--       --     (stop acc) →
--       --       isoFunInjective (invIso ⟜UMP) _ _
--       --         ((λ i →
--       --           {!!}) ∙
--       --           -- ⟜-app
--       --           -- ∘g {!!} ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ∙
--       --           {!!})
--       --           -- {!!}
--       --           -- ∘g rec _ ⊗Alg (inl q)
--       --           -- ∘g ⟜-β (
--       --           --   STEPε ⊗NFA (N-acc q acc)
--       --           --   ∘g rec _ N'Alg (N' .init)
--       --           --   ∘g ⊗-unit-l) i
--       --           -- ∘g (lowerG ∘g lowerG) ,⊗ id)
--       --   ; (step t Eq.refl) → {!!}
--       --     -- (λ i →
--       --     --   {!!}
--       --     --   ∘g ⊗Alg→initial .snd (inl q) i
--       --     --   ∘g ⊕ᴰ-in (step (inl t) Eq.refl)
--       --     --   ∘g (liftG ∘g liftG) ,⊗ {!liftG!}
--       --     --   ∘g (lowerG ∘g lowerG) ,⊗ lowerG)
--       --   ; (stepε t Eq.refl) → {!!} }

-- -- -- --   opaque
-- -- -- --     unfolding AlgebraHom-seq ∃AlgebraHom recTrace P-initial !PAlgebraHom' P-idAlgebraHom
-- -- -- --     ⊗-strong-equivalence :
-- -- -- --       StrongEquivalence (InitParse ⊗NFA) (InitParse N ⊗ InitParse N')
-- -- -- --     ⊗-strong-equivalence = mkStrEq
-- -- -- --       (recInit _ ⊗Alg)
-- -- -- --       (P-recInit _ _ NPAlg)
-- -- -- --       (!PAlgebraHom' _ _ NPAlg' Prec (P-idAlgebraHom _ _ _) _)
-- -- -- --       (algebra-η ⊗NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊗Alg) ⊗Alg→initial))
-- -- -- --       where
-- -- -- --         ⊗Alg : Algebra ⊗NFA
-- -- -- --         ⊗Alg .the-ℓs (inl q) = _
-- -- -- --         ⊗Alg .the-ℓs (inr q') = _
-- -- -- --         ⊗Alg .G (inl q) = Parse N q ⊗ InitParse N'
-- -- -- --         ⊗Alg .G (inr q') = Parse N' q'
-- -- -- --         ⊗Alg .nil-case {inr q'} acc = nil (lower acc)
-- -- -- --         ⊗Alg .cons-case (inl t) =
-- -- -- --           ⊗-intro (cons t) id
-- -- -- --           ∘g ⊗-assoc
-- -- -- --         ⊗Alg .cons-case (inr t') = cons t'
-- -- -- --         ⊗Alg .ε-cons-case (N-acc q acc) =
-- -- -- --           ⊗-intro (nil acc) id
-- -- -- --           ∘g ⊗-unit-l⁻
-- -- -- --         ⊗Alg .ε-cons-case (N-ε-trans t) =
-- -- -- --           ⊗-intro (ε-cons t) id
-- -- -- --         ⊗Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

-- -- -- --         N'Alg : Algebra N'
-- -- -- --         N'Alg .the-ℓs = _
-- -- -- --         N'Alg .G q' = Parse ⊗NFA (inr q')
-- -- -- --         N'Alg .nil-case acc' = nil (lift acc')
-- -- -- --         N'Alg .cons-case t' = cons (inr t')
-- -- -- --         N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

-- -- -- --         NPAlg : PAlgebra N (InitParse N')
-- -- -- --         NPAlg .the-ℓs = _
-- -- -- --         NPAlg .G q = Parse ⊗NFA (inl q)
-- -- -- --         NPAlg .nil-case acc =
-- -- ε-cons (N-acc _ acc) ∘g recInit _ N'Alg
-- -- -- --         NPAlg .cons-case t = cons (inl t)
-- -- -- --         NPAlg .ε-cons-case t = ε-cons (N-ε-trans t)

-- -- -- --         NPAlg' : PAlgebra N (InitParse N')
-- -- -- --         NPAlg' .the-ℓs = _
-- -- -- --         NPAlg' .G q = Parse N q ⊗ InitParse N'
-- -- -- --         NPAlg' .nil-case acc =
-- -- ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
-- -- -- --         NPAlg' .cons-case t =
-- -- ⊗-intro (cons t) id ∘g ⊗-assoc
-- -- -- --         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

-- -- -- --         N'≅⊗NFA⟨inr⟩ :
-- -- recTrace _ ⊗Alg ∘g recInit _ N'Alg ≡ id
-- -- -- --         N'≅⊗NFA⟨inr⟩ =
-- -- -- --           algebra-η N'
-- -- (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
-- -- -- --             { f = λ q → recTrace _ ⊗Alg
-- -- -- --             ; on-nil = λ _ → refl
-- -- -- --             ; on-cons = λ _ → refl
-- -- -- --             ; on-ε-cons = λ _ → refl }))

-- -- -- --         ⊗Alg→initial : AlgebraHom ⊗NFA ⊗Alg (initial ⊗NFA)
-- -- -- --         ⊗Alg→initial .f (inl q) = P-recTrace _ _ NPAlg
-- -- -- --         ⊗Alg→initial .f (inr q') = recTrace _ N'Alg
-- -- -- --         ⊗Alg→initial .on-nil {inr q'} _ = refl
-- -- -- --         ⊗Alg→initial .on-cons (inl t) =
-- -- -- --            (λ i → ⟜-β ((cons (inl t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)) i ∘g
-- -- -- --              ⊗-intro (⊗-intro id (recTrace _ (underlyingAlg _ _ NPAlg))) id ∘g
-- -- -- --                ⊗-assoc) ∙
-- -- -- --             (λ i → cons (inl t) ∘g ⊗-intro id (P-recTrace _ _ NPAlg) ∘g
-- -- -- --               ⊗-assoc⁻∘⊗-assoc≡id i)
-- -- -- --         ⊗Alg→initial .on-cons (inr t) = refl
-- -- -- --         ⊗Alg→initial .on-ε-cons (N-acc _ acc) =
-- -- -- --           ((λ i →
-- -- -- --              ⟜-β (ε-cons (N-acc _ acc) ∘g
-- -- -- --                recInit _ N'Alg ∘g
-- -- -- --                  ⊗-unit-l) i ∘g
-- -- -- --                  ⊗-unit-l⁻) ∙
-- -- -- --           (λ i → ε-cons (N-acc _ acc) ∘g
-- -- -- --           recInit _ N'Alg ∘g ⊗-unit-l⁻l i))
-- -- -- --         ⊗Alg→initial .on-ε-cons (N-ε-trans t) =
-- -- -- --           (λ i → ⟜-β (ε-cons (N-ε-trans t) ∘g ⟜-app) i ∘g
-- -- -- --              ⊗-intro (recTrace _ (underlyingAlg _ _ NPAlg)) id)
-- -- -- --         ⊗Alg→initial .on-ε-cons (N'-ε-trans t') = refl

-- -- -- --         Prec : PAlgebraHom _ _ (P-initial N (InitParse N')) NPAlg'
-- -- -- --         Prec .f q =
-- -- -- --           recTrace ⊗NFA ⊗Alg ∘g
-- -- -- --           P-recTrace _ _ NPAlg
-- -- -- --         Prec .on-nil qAcc =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g (⟜-β
-- -- -- --               ((ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg) ∘g ⊗-unit-l) i) ∘g
-- -- -- --                ⊗-unit-l⁻) ∙
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g
-- -- -- --             ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg ∘g ⊗-unit-l⁻l i) ∙
-- -- -- --           (λ i → ⊗-intro (nil qAcc) id ∘g ⊗-unit-l⁻ ∘g N'≅⊗NFA⟨inr⟩ i)
-- -- -- --         Prec .on-cons t =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g
-- -- -- --             ⊗Alg→initial .on-cons (inl t) i)
-- -- -- --         Prec .on-ε-cons t =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g
-- -- -- --             ⊗Alg→initial .on-ε-cons (N-ε-trans t) i)

-- -- -- --     ⊗-strong-equivalence' :
-- -- -- --       StrongEquivalence (InitParse ⊗NFA) (InitParse N ⊗ InitParse N')
-- -- -- --     ⊗-strong-equivalence' = mkStrEq
-- -- -- --       (recInit _ ⊗Alg)
-- -- -- --       (P-recInit' _ _ NPAlg)
-- -- -- --       (!PAlgebraHom' _ _ NPAlg' Prec (P-idAlgebraHom _ _ _) _)
-- -- -- --       (algebra-η ⊗NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊗Alg) ⊗Alg→initial))
-- -- -- --       where
-- -- -- --         ⊗Alg : Algebra ⊗NFA
-- -- -- --         ⊗Alg .the-ℓs (inl q) = _
-- -- -- --         ⊗Alg .the-ℓs (inr q') = _
-- -- -- --         ⊗Alg .G (inl q) = Parse N q ⊗ InitParse N'
-- -- -- --         ⊗Alg .G (inr q') = Parse N' q'
-- -- -- --         ⊗Alg .nil-case {inr q'} acc = nil (lower acc)
-- -- -- --         ⊗Alg .cons-case (inl t) =
-- -- -- --           ⊗-intro (cons t) id
-- -- -- --           ∘g ⊗-assoc
-- -- -- --         ⊗Alg .cons-case (inr t') = cons t'
-- -- -- --         ⊗Alg .ε-cons-case (N-acc q acc) =
-- -- -- --           ⊗-intro (nil acc) id
-- -- -- --           ∘g ⊗-unit-l⁻
-- -- -- --         ⊗Alg .ε-cons-case (N-ε-trans t) =
-- -- -- --           ⊗-intro (ε-cons t) id
-- -- -- --         ⊗Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

-- -- -- --         N'Alg : Algebra N'
-- -- -- --         N'Alg .the-ℓs = _
-- -- -- --         N'Alg .G q' = Parse ⊗NFA (inr q')
-- -- -- --         N'Alg .nil-case acc' = nil (lift acc')
-- -- -- --         N'Alg .cons-case t' = cons (inr t')
-- -- -- --         N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

-- -- -- --         NPAlg : PAlgebra N (InitParse N')
-- -- -- --         NPAlg .the-ℓs = _
-- -- -- --         NPAlg .G q = Parse ⊗NFA (inl q)
-- -- -- --         NPAlg .nil-case acc = ε-cons (N-acc _ acc) ∘g recInit _ N'Alg
-- -- -- --         NPAlg .cons-case t = cons (inl t)
-- -- -- --         NPAlg .ε-cons-case t = ε-cons (N-ε-trans t)

-- -- -- --         NPAlg' : PAlgebra N (InitParse N')
-- -- -- --         NPAlg' .the-ℓs = _
-- -- -- --         NPAlg' .G q = Parse N q ⊗ InitParse N'
-- -- -- --         NPAlg' .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
-- -- -- --         NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
-- -- -- --         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id
-- -- -- --         N'≅⊗NFA⟨inr⟩ : recTrace _ ⊗Alg ∘g recInit _ N'Alg ≡ id
-- -- -- --         N'≅⊗NFA⟨inr⟩ =
-- -- -- --           algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
-- -- -- --             { f = λ q → recTrace _ ⊗Alg
-- -- -- --             ; on-nil = λ _ → refl
-- -- -- --             ; on-cons = λ _ → refl
-- -- -- --             ; on-ε-cons = λ _ → refl }))
-- -- -- --         ⊗Alg→initial : AlgebraHom ⊗NFA ⊗Alg (initial ⊗NFA)
-- -- -- --         ⊗Alg→initial .f (inl q) = P-recTrace' _ _ NPAlg
-- -- -- --         ⊗Alg→initial .f (inr q') = recTrace _ N'Alg
-- -- -- --         ⊗Alg→initial .on-nil {inr q'} _ = refl
-- -- -- --         ⊗Alg→initial .on-cons (inl t) =
-- -- -- --           λ i → cons (inl t) ∘g ⊗-intro id (P-recTrace' _ _ NPAlg) ∘g
-- -- -- --             ⊗-assoc⁻∘⊗-assoc≡id i
-- -- -- --         ⊗Alg→initial .on-cons (inr t) = refl
-- -- -- --         ⊗Alg→initial .on-ε-cons (N-acc q x) =
-- -- -- --           λ i → ε-cons (N-acc q x) ∘g recTrace _ N'Alg ∘g ⊗-unit-l⁻l i
-- -- -- --         ⊗Alg→initial .on-ε-cons (N-ε-trans x) = refl
-- -- -- --         ⊗Alg→initial .on-ε-cons (N'-ε-trans x) = refl

-- -- -- --         Prec : PAlgebraHom _ _ (P-initial N (InitParse N')) NPAlg'
-- -- -- --         Prec .f q = recTrace _ ⊗Alg ∘g P-recTrace' _ _ NPAlg
-- -- -- --         Prec .on-nil qAcc =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g
-- -- -- --             ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg ∘g ⊗-unit-l⁻l i) ∙
-- -- -- --           (λ i → ⊗-intro (nil qAcc) id ∘g ⊗-unit-l⁻ ∘g N'≅⊗NFA⟨inr⟩ i)
-- -- -- --         Prec .on-cons t =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g ⊗Alg→initial .on-cons (inl t) i)
-- -- -- --         Prec .on-ε-cons t =
-- -- -- --           (λ i → recTrace _ ⊗Alg ∘g ⊗Alg→initial .on-ε-cons (N-ε-trans t) i)

-- -- -- -- -- Kleene Star
-- -- -- -- module _ (N : NFA {ℓN}) where
-- -- -- --   data *εTrans : Type ℓN where
-- -- -- --     inr : *εTrans
-- -- -- --     cons⟨N⟩ : ∀ {q} → ⟨ N .isAcc q .fst ⟩ → *εTrans
-- -- -- --     N-internal : ⟨ N .ε-transition ⟩ → *εTrans

-- -- -- --   *εTrans-rep :
-- -- -- --     (Unit ⊎ ((Σ[ q ∈ _ ] ⟨ N .isAcc q .fst ⟩) ⊎ ⟨ N .ε-transition ⟩)) ≃ *εTrans
-- -- -- --   *εTrans-rep = isoToEquiv
-- -- -- --     (iso
-- -- -- --       (λ { (inl x) → inr
-- -- -- --          ; (inr (inl x)) → cons⟨N⟩ (x .snd)
-- -- -- --          ; (inr (inr x)) → N-internal x })
-- -- -- --       (λ { inr → inl tt
-- -- -- --          ; (cons⟨N⟩ x) → inr (inl (_ , x))
-- -- -- --          ; (N-internal x) → inr (inr x)})
-- -- -- --       (λ { inr → refl ; (cons⟨N⟩ x) → refl ; (N-internal x) → refl })
-- -- -- --       λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl })

-- -- -- --   *NFA : NFA {ℓN}
-- -- -- --   *NFA .Q = Unit ⊎ N .Q .fst , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
-- -- -- --   *NFA .init = inl _
-- -- -- --   *NFA .isAcc (inl _) = (Unit* , isPropUnit*) , (yes _)
-- -- -- --   *NFA .isAcc (inr q) = (Empty.⊥* , isProp⊥*) , no lower
-- -- -- --   *NFA .transition = N .transition
-- -- -- --   *NFA .src = inr ∘ N .src
-- -- -- --   *NFA .dst = inr ∘ N .dst
-- -- -- --   *NFA .label = N .label
-- -- -- --   *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
-- -- -- --     (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ ,
-- -- -- --       isFinSetΣ (N .Q) (λ q → _ ,
-- -- -- --        isDecProp→isFinSet
-- -- -- --        (N .isAcc q .fst .snd) (N .isAcc q .snd))) (N .ε-transition)))
-- -- -- --   *NFA .ε-src inr = inl _
-- -- -- --   *NFA .ε-dst inr = inr (N .init)
-- -- -- --   *NFA .ε-src (cons⟨N⟩ {q} _) = inr q
-- -- -- --   *NFA .ε-dst (cons⟨N⟩ {q} _) = inl _
-- -- -- --   *NFA .ε-src (N-internal t) = inr (N .ε-src t)
-- -- -- --   *NFA .ε-dst (N-internal t) = inr (N .ε-dst t)

-- -- -- --   opaque
-- -- -- --     unfolding ⊗-unit-l⁻ ⊗-unit-l *r-initial KL*r-elim id*r-AlgebraHom AlgebraHom-seq ∃AlgebraHom recTrace P-initial !PAlgebraHom' P-idAlgebraHom
-- -- -- --     *-strong-equivalence :
-- -- -- --       StrongEquivalence (InitParse *NFA) (KL* (InitParse N))
-- -- -- --     *-strong-equivalence = mkStrEq
-- -- -- --       (recInit *NFA *Alg)
-- -- -- --       (foldKL*r (InitParse N) the-KL*-alg)
-- -- -- --       (!*r-AlgebraHom (InitParse N) (*r-initial (InitParse N))
-- -- -- --         (record { f = recInit *NFA *Alg ∘g foldKL*r (InitParse N) the-KL*-alg
-- -- -- --                 ; on-nil = refl
-- -- -- --                 ; on-cons = (λ i → KL*.cons ∘g
-- -- -- --                   nested-induction-lemma i ∘g ⊗-intro id (foldKL*r _ the-KL*-alg))
-- -- -- --         })
-- -- -- --         (id*r-AlgebraHom _ _))
-- -- -- --       (algebra-η *NFA (AlgebraHom-seq _ (∃AlgebraHom _ *Alg)
-- -- -- --         (record { f = λ {
-- -- -- --                     (inl _) → foldKL*r _ the-KL*-alg
-- -- -- --                   ; (inr q) → P-recTrace' _ _ NPAlg ∘g
-- -- -- --                               ⊗-intro id (foldKL*r _ the-KL*-alg) }
-- -- -- --                 ; on-nil = λ { {inl _} acc → refl }
-- -- -- --                 ; on-cons = λ { t → λ i → cons t ∘g ⊗-intro id
-- -- -- --                (P-recTrace' N (InitParse *NFA) NPAlg ∘g
-- -- -- --                  ⊗-intro id (foldKL*r (InitParse N) the-KL*-alg))
-- -- -- --                  ∘g ⊗-assoc⁻∘⊗-assoc≡id i }
-- -- -- --                 ; on-ε-cons = λ {
-- -- -- --                     inr → refl
-- -- -- --                   ; (cons⟨N⟩ x) →
-- -- -- --                     λ i → ε-cons (cons⟨N⟩ x) ∘g
-- -- -- --                       ⊗-unit-l⁻l i ∘g foldKL*r (InitParse N) the-KL*-alg
-- -- -- --                   ; (N-internal x) → refl } })))
-- -- -- --       where
-- -- -- --         *Alg : Algebra *NFA
-- -- -- --         *Alg .the-ℓs (inl _) = _
-- -- -- --         *Alg .the-ℓs (inr q) = _
-- -- -- --         *Alg .G (inl _) = KL* (InitParse N)
-- -- -- --         *Alg .G (inr q) = Parse N q ⊗ KL* (InitParse N)
-- -- -- --         *Alg .nil-case {q = inl x} _ = KL*.nil
-- -- -- --         *Alg .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
-- -- -- --         *Alg .ε-cons-case inr = KL*.cons
-- -- -- --         *Alg .ε-cons-case (cons⟨N⟩ acc) = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
-- -- -- --         *Alg .ε-cons-case (N-internal t) = ⊗-intro (ε-cons t) id

-- -- -- --         -- given a parse starting at q in N and a *NFA parse, make a
-- -- -- --         -- *NFA parse starting at q.
-- -- -- --         NPAlg : PAlgebra N (InitParse *NFA)
-- -- -- --         NPAlg .the-ℓs = _
-- -- -- --         NPAlg .G q = Parse *NFA (inr q)
-- -- -- --         NPAlg .nil-case acc = ε-cons (cons⟨N⟩ acc)
-- -- -- --         NPAlg .cons-case t = cons t
-- -- -- --         NPAlg .ε-cons-case t = ε-cons (N-internal t)

-- -- -- --         open *r-Algebra
-- -- -- --         -- NOTE : this is not an algebra for NFAs, rather for Kleene star
-- -- -- --         -- and is used to prove the uniqueness of the foldKL*r term
-- -- -- --         the-KL*-alg : *r-Algebra (InitParse N)
-- -- -- --         the-KL*-alg .the-ℓ = _
-- -- -- --         the-KL*-alg .G = InitParse *NFA
-- -- -- --         the-KL*-alg .nil-case = nil _
-- -- -- --         the-KL*-alg .cons-case = ε-cons inr ∘g P-recInit' _ _ NPAlg

-- -- -- --         NPAlg' : PAlgebra N (InitParse *NFA)
-- -- -- --         NPAlg' .the-ℓs = _
-- -- -- --         NPAlg' .G q = Parse N q ⊗ KL* (InitParse N)
-- -- -- --         NPAlg' .nil-case acc = ⊗-intro (nil acc) (recInit _ *Alg) ∘g ⊗-unit-l⁻
-- -- -- --         NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
-- -- -- --         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

-- -- -- --         nested-induction-lemma :
-- -- -- --           Path (InitParse N ⊗ InitParse *NFA ⊢ InitParse N ⊗ KL* (InitParse N))
-- -- -- --             (recTrace *NFA *Alg ∘g P-recInit' _ _ NPAlg)
-- -- -- --             (⊗-intro id (recInit *NFA *Alg))
-- -- -- --         nested-induction-lemma =
-- -- -- --           !PAlgebraHom' _ _ NPAlg'
-- -- -- --             rec*Alg∘recInitNPAlgHom
-- -- -- --             recInit*AlgHom
-- -- -- --             _
-- -- -- --           where
-- -- -- --             rec*Alg∘recInitNPAlgHom : PAlgebraHom N (InitParse *NFA)
-- -- -- --               (P-initial N (InitParse *NFA))
-- -- -- --               NPAlg'
-- -- -- --             rec*Alg∘recInitNPAlgHom .f q =
-- -- -- --               recTrace *NFA *Alg ∘g P-recTrace' _ _ NPAlg
-- -- -- --             rec*Alg∘recInitNPAlgHom .on-nil acc =
-- -- -- --               λ i → ⊗-intro (nil acc) (recInit *NFA *Alg) ∘g
-- -- -- --                 ⊗-unit-ll⁻ i ∘g ⊗-unit-l⁻
-- -- -- --             rec*Alg∘recInitNPAlgHom .on-cons t =
-- -- -- --               λ i → (⊗-intro (cons t) id ∘g ⊗-assoc) ∘g
-- -- -- --                 ⊗-intro id (recTrace *NFA *Alg ∘g
-- -- -- --                   P-recTrace' N (InitParse *NFA) NPAlg) ∘g ⊗-assoc⁻∘⊗-assoc≡id i
-- -- -- --             rec*Alg∘recInitNPAlgHom .on-ε-cons t = refl

-- -- -- --             recInit*AlgHom :
-- -- -- --               PAlgebraHom N
-- -- -- --                 (InitParse *NFA) (P-initial N (InitParse *NFA)) NPAlg'
-- -- -- --             recInit*AlgHom .f q = ⊗-intro id (recTrace _ *Alg)
-- -- -- --             recInit*AlgHom .on-nil acc = refl
-- -- -- --             recInit*AlgHom .on-cons t = refl
-- -- -- --             recInit*AlgHom .on-ε-cons t = refl
