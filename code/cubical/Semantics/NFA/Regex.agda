open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module Semantics.NFA.Regex ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
import      Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.More
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Unit

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.DFA
open import Semantics.NFA.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFA
open Algebra
open AlgebraHom

-- This file constructs NFAs that are strongly equivalent to
-- regular expressions.
--
-- For each constructor of a regular expression, we build
-- a corresponding NFA. And then we inductively combine smaller
-- NFAs into one machine that is equivalent to the regex

-- Literal
-- Accepts only a single character c, drawn from alphabet Σ₀
module _ (c : Σ₀) where
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

  literalNFA : NFA {ℓ-zero}
  literalNFA .Q = STATE , 2 , ∣ isoToEquiv STATE≅Fin2 ∣₁
  literalNFA .init = c-st
  literalNFA .isAcc q =
    ( (q Eq.≡ ε-st)
    , isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (isSetSTATE _ _))
    , EquivPresDec (isoToEquiv Eq.PathIsoEq) (isDiscSTATE _ _)
  literalNFA .transition = Unit , isFinSetUnit
  literalNFA .src _ = c-st
  literalNFA .dst _ = ε-st
  literalNFA .label _ = c
  literalNFA .ε-transition = ⊥ , isFinSet⊥
  literalNFA .ε-src = ⊥.rec
  literalNFA .ε-dst = ⊥.rec

  litNFA-strong-equiv : StrongEquivalence (InitParse literalNFA) (literal c)
  litNFA-strong-equiv = mkStrEq
    (recInit _ litAlg)
    the-inv
    ⊗-unit-r⁻r
    (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ litAlg) (record
      { f = λ { c-st → the-inv ; ε-st → nil Eq.refl }
      ; on-nil = λ { Eq.refl → refl }
      ; on-cons = λ _ → λ i →
        cons _
        ∘g (⊗-intro id (nil Eq.refl))
        ∘g ⊗-unit-rr⁻ i
      ; on-ε-cons = ⊥.elim })))
    where
      the-inv : literal c ⊢ InitParse literalNFA
      the-inv =
        cons _
        ∘g ⊗-intro id (nil Eq.refl)
        ∘g ⊗-unit-r⁻

      litAlg : Algebra literalNFA
      litAlg .the-ℓs _ = ℓ-zero
      litAlg .G c-st = literal c
      litAlg .G ε-st = ε-grammar
      litAlg .nil-case Eq.refl = id
      litAlg .cons-case _ = ⊗-unit-r
      litAlg .ε-cons-case = ⊥.elim

-- Nullary Disjunction
module _ where
  emptyNFA : NFA {ℓ-zero}
  emptyNFA .Q = Unit , isFinSetUnit
  emptyNFA .init = tt
  emptyNFA .isAcc _ = (⊥ , isProp⊥) , no (λ z → z) -- todo: upstream this def
  emptyNFA .transition = ⊥ , isFinSet⊥
  emptyNFA .src = ⊥.elim
  emptyNFA .dst = ⊥.elim
  emptyNFA .label = ⊥.elim
  emptyNFA .ε-transition = ⊥ , isFinSet⊥
  emptyNFA .ε-src = ⊥.rec
  emptyNFA .ε-dst = ⊥.rec

  emptyNFA-strong-equiv :
    StrongEquivalence (InitParse emptyNFA) ⊥-grammar
  emptyNFA-strong-equiv = mkStrEq
    (recInit _ ⊥Alg)
    ⊥-elim
    (⊥-η _ _)
    (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ ⊥Alg)
      (record { f = λ _ → ⊥-elim
              ; on-nil = ⊥.elim
              ; on-cons = ⊥.elim
              ; on-ε-cons = ⊥.elim })))
    where
      ⊥Alg : Algebra emptyNFA
      ⊥Alg .the-ℓs = _
      ⊥Alg .G _ = ⊥-grammar
      ⊥Alg .nil-case = ⊥.elim
      ⊥Alg .cons-case = ⊥.elim
      ⊥Alg .ε-cons-case = ⊥.elim

-- Binary Disjunction
-- Given two NFAs N and N', accepts a string if and only if
-- the string is accept by N or by N'
module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
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

  ⊕NFA : NFA
  ⊕NFA .Q = ⊕State , EquivPresIsFinSet (invEquiv ⊕State-rep)
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (N .Q) (N' .Q)))
  ⊕NFA .init = start
  ⊕NFA .isAcc = λ { start → (⊥* , isProp⊥*) , (no lower)
    ; (inl q) → LiftDecProp'' {ℓN} {ℓN'} (N .isAcc q)
    ; (inr q') → LiftDecProp'' {ℓN'} {ℓN} (N' .isAcc q') }
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

  ⊕-strong-equivalence :
    StrongEquivalence (InitParse ⊕NFA) (InitParse N ⊕ InitParse N')
  ⊕-strong-equivalence = mkStrEq
    (recInit _ ⊕Alg)
    inj-parse
    (⊕≡ _ _
      (λ i → ⊕-inl ∘g N-retr i)
      λ i → ⊕-inr ∘g N'-retr i)
    (algebra-η ⊕NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊕Alg) (record
      { f = λ { start → inj-parse
              ; (inl x) → recTrace _ NAlg
              ; (inr x) → recTrace _ N'Alg }
      ; on-nil = λ { {start} → ⊥.elim*
                   ; {inl x} → λ _ → refl
                   ; {inr x} → λ _ → refl }
      ; on-cons = λ { (inl x) → refl ; (inr x) → refl }
      ; on-ε-cons = λ { pick-inl → refl
        ; pick-inr → refl
        ; (N-ε-trans x) → refl
        ; (N'-ε-trans x) → refl
        } })))
    where
      ⊕Alg : Algebra ⊕NFA
      ⊕Alg .the-ℓs start = (ℓ-max ℓN ℓN')
      ⊕Alg .the-ℓs (inl _) = ℓN
      ⊕Alg .the-ℓs (inr _) = ℓN'
      ⊕Alg .G start = InitParse N ⊕ InitParse N'
      ⊕Alg .G (inl q)  = Parse N q
      ⊕Alg .G (inr q') = Parse N' q'
      ⊕Alg .nil-case {start} ()
      ⊕Alg .nil-case {inl x} acc  = nil (lower acc)
      ⊕Alg .nil-case {inr x} acc' = nil (lower acc')
      ⊕Alg .cons-case (inl t)  = cons t
      ⊕Alg .cons-case (inr t') = cons t'
      ⊕Alg .ε-cons-case pick-inl = ⊕-inl
      ⊕Alg .ε-cons-case pick-inr = ⊕-inr
      ⊕Alg .ε-cons-case (N-ε-trans t) = ε-cons t
      ⊕Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

      NAlg : Algebra N
      NAlg .the-ℓs = _
      NAlg .G q = Parse ⊕NFA (inl q)
      NAlg .nil-case acc = nil (lift acc)
      NAlg .cons-case t = cons (inl t)
      NAlg .ε-cons-case t = ε-cons (N-ε-trans t)

      N'Alg : Algebra N'
      N'Alg .the-ℓs = _
      N'Alg .G q = Parse ⊕NFA (inr q)
      N'Alg .nil-case acc' = nil (lift acc')
      N'Alg .cons-case t' = cons (inr t')
      N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

      inj-parse : Term (InitParse N ⊕ InitParse N') (Parse ⊕NFA start)
      inj-parse = (⊕-elim
        (ε-cons pick-inl ∘g recInit _ NAlg)
        (ε-cons pick-inr ∘g recInit _ N'Alg))

      N-retr : recTrace _ ⊕Alg ∘g recInit _ NAlg ≡ id
      N-retr = algebra-η N (AlgebraHom-seq _ (∃AlgebraHom _ NAlg) (record
        { f = λ q → recTrace _ ⊕Alg
        ; on-nil = λ _ → refl
        ; on-cons = λ _ → refl
        ; on-ε-cons = λ _ → refl }))
      N'-retr : recTrace _ ⊕Alg ∘g recInit _ N'Alg ≡ id
      N'-retr = algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
        { f = λ q → recTrace _ ⊕Alg
        ; on-nil = λ _ → refl
        ; on-cons = λ _ → refl
        ; on-ε-cons = λ _ → refl
        }))

-- Epsilon, the nullary sequencing
module _ where
  -- an NFA with one state,
  -- no transitions,
  -- and the single state is both initial and accepting
  εNFA : NFA {ℓ-zero}
  εNFA .Q = Unit , isFinSetUnit
  εNFA .init = tt
  εNFA .isAcc = λ x → (Unit , isPropUnit) , (yes _)
  εNFA .transition = ⊥ , isFinSet⊥
  εNFA .src = ⊥.rec
  εNFA .dst = ⊥.rec
  εNFA .label = ⊥.rec
  εNFA .ε-transition = ⊥ , isFinSet⊥
  εNFA .ε-src = ⊥.rec
  εNFA .ε-dst = ⊥.rec

  εNFA-strong-equiv :
    StrongEquivalence (InitParse εNFA) ε-grammar
  εNFA-strong-equiv = mkStrEq
    (recInit _ εAlg)
    (nil _)
    refl
    (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ εAlg) (record
      { f = λ _ → nil _
      ; on-nil = λ _ → refl
      ; on-cons = ⊥.elim
      ; on-ε-cons = ⊥.elim })))
    where
      εAlg : Algebra εNFA
      εAlg .the-ℓs = _
      εAlg .G = λ _ → ε-grammar
      εAlg .nil-case = λ _ → id
      εAlg .cons-case = ⊥.elim
      εAlg .ε-cons-case = ⊥.elim

-- Concatenation
-- Given two NFAs N and N', accepts a string w if and only if
-- w ≡ w₁ ++ w₂ where w₁ is accepted by N and w₂ accepted by N'
module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
  ⊗State : FinSet (ℓ-max ℓN ℓN')
  ⊗State .fst = ⟨ N .Q ⟩ ⊎ ⟨ N' .Q ⟩
  ⊗State .snd = isFinSet⊎ (N .Q) (N' .Q)

  ⊗Trans : FinSet (ℓ-max ℓN ℓN')
  ⊗Trans .fst = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
  ⊗Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊗εTrans : Type (ℓ-max ℓN ℓN') where
    N-acc : ∀ q → (N .isAcc q .fst .fst) → ⊗εTrans
    N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊗εTrans
    N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊗εTrans

  ⊗εTrans-rep :
    (Σ[ q ∈ ⟨ N .Q ⟩ ] (N .isAcc q .fst .fst)) ⊎
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

  ⊗NFA : NFA
  ⊗NFA .Q = ⊗State
  ⊗NFA .init = inl (N .init)
  ⊗NFA .isAcc = λ { (inl q) → (⊥* , isProp⊥*) , (no lower)
                  ; (inr q') → LiftDecProp'' {ℓN'}{ℓN} (N' .isAcc q')}
  ⊗NFA .transition = ⊗Trans
  ⊗NFA .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
  ⊗NFA .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
  ⊗NFA .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
  ⊗NFA .ε-transition =
    ⊗εTrans ,
    EquivPresIsFinSet ⊗εTrans-rep
      (isFinSet⊎
        (_ , isFinSetΣ (N .Q)
          (λ q → _ ,
            isDecProp→isFinSet (N .isAcc q .fst .snd) (N .isAcc q .snd)))
        (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
  ⊗NFA .ε-src = λ { (N-acc q qAcc) → inl q
                  ; (N-ε-trans t) → inl (N .ε-src t)
                  ; (N'-ε-trans t') → inr (N' .ε-src t') }
  ⊗NFA .ε-dst = λ { (N-acc q qAcc) → inr (N' .init)
                  ; (N-ε-trans t) → inl (N .ε-dst t)
                  ; (N'-ε-trans t') → inr (N' .ε-dst t') }

  ⊗-strong-equivalence :
    StrongEquivalence (InitParse ⊗NFA) (InitParse N ⊗ InitParse N')
  ⊗-strong-equivalence = mkStrEq
    (recInit _ ⊗Alg)
    (⟜-app ∘g ⊗-intro (recInit _ NAlg) id)
    (isoFunInjective ⟜UMP _ _ (!AlgebraHom' N NAlg' λrec λid (N .init)))
    (algebra-η ⊗NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊗Alg) (record
    { f = λ { (inl q) → ⟜-app ∘g ⊗-intro (recTrace _ NAlg) id
            ; (inr q') → recTrace _ N'Alg }
    ; on-nil = λ { {inl q} → ⊥.elim*
                 ; {inr q'} → λ _ → refl }
      -- cons
    ; on-cons = λ { (inl t ) →
      (⟜-app
      ∘g ⊗-intro (⟜-intro {k = Parse _ _} (cons (inl t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)) id
      ∘g ⊗-intro (⊗-intro id (recTrace N NAlg)) id
      ∘g ⊗-assoc)
         ≡⟨ (λ i → ⟜-β ((cons (inl t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)) i ∘g ⊗-intro (⊗-intro id (recTrace N NAlg)) id ∘g ⊗-assoc) ⟩
      (cons (inl t)
      ∘g ⊗-intro id ⟜-app
      ∘g ⊗-intro id (⊗-intro (recTrace N NAlg) id)
      ∘g ⊗-assoc⁻
      ∘g ⊗-assoc)
         ≡⟨ (λ i → cons (inl t) ∘g ⊗-intro id (⟜-app ∘g ⊗-intro (recTrace N NAlg) id) ∘g ⊗-assoc⁻∘⊗-assoc≡id i) ⟩
      (cons (inl t)
      ∘g ⊗-intro id (⟜-app ∘g ⊗-intro (recTrace N NAlg) id))
      ∎
                  ; (inr t') → refl }
    ; on-ε-cons = λ { (N-acc q acc) →
      (λ i → ⟜-β (ε-cons (N-acc _ acc) ∘g recInit _ N'Alg ∘g ⊗-unit-l) i ∘g ⊗-unit-l⁻)
      ∙ λ i → ε-cons (N-acc _ acc) ∘g recInit _ N'Alg ∘g ⊗-unit-l⁻l i
                    ; (N-ε-trans t) →
        λ i → ⟜-β (ε-cons (N-ε-trans t) ∘g ⟜-app) i ∘g ⊗-intro (recTrace N NAlg) id
                    ; (N'-ε-trans t') → refl } })))
    where
      ⊗Alg : Algebra ⊗NFA
      ⊗Alg .the-ℓs (inl q) = _
      ⊗Alg .the-ℓs (inr q') = _
      ⊗Alg .G (inl q) = Parse N q ⊗ InitParse N'
      ⊗Alg .G (inr q') = Parse N' q'
      ⊗Alg .nil-case {inr q'} acc = nil (lower acc)
      ⊗Alg .cons-case (inl t) =
        ⊗-intro (cons t) id
        ∘g ⊗-assoc
      ⊗Alg .cons-case (inr t') = cons t'
      ⊗Alg .ε-cons-case (N-acc q acc) =
        ⊗-intro (nil acc) id
        ∘g ⊗-unit-l⁻
      ⊗Alg .ε-cons-case (N-ε-trans t) =
        ⊗-intro (ε-cons t) id
      ⊗Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

      N'Alg : Algebra N'
      N'Alg .the-ℓs = _
      N'Alg .G q' = Parse ⊗NFA (inr q')
      N'Alg .nil-case acc' = nil (lift acc')
      N'Alg .cons-case t' = cons (inr t')
      N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

      NAlg : Algebra N
      NAlg .the-ℓs = _
      NAlg .G q = Parse ⊗NFA (inl q) ⊗- InitParse N'
      NAlg .nil-case acc =
        ⟜-intro (ε-cons (N-acc _ acc)
          ∘g recInit _ N'Alg
          ∘g ⊗-unit-l)
      NAlg .cons-case t =
        ⟜-intro {k = Parse _ _} (cons (inl t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)
      NAlg .ε-cons-case t =
        ⟜-intro {k = Parse _ _} (ε-cons (N-ε-trans t) ∘g ⟜-app)
      open PAlgebra
      NPalg : PAlgebra N (InitParse N')
      NPalg .the-ℓs = _
      NPalg .G q = Parse ⊗NFA (inl q)
      NPalg .nil-case acc = ε-cons (N-acc _ acc) ∘g recInit _ N'Alg
      NPalg .cons-case t = cons (inl t)
      NPalg .ε-cons-case t = ε-cons (N-ε-trans t)

      NPAlg' : PAlgebra N (InitParse N')
      NPAlg' .the-ℓs = _
      NPAlg' .G q = Parse N q ⊗ InitParse N'
      NPAlg' .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
      NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
      NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

      NAlg' : Algebra N
      NAlg' .the-ℓs = _
      NAlg' .G q = (Parse N q ⊗ InitParse N') ⊗- InitParse N'
      NAlg' .nil-case acc = ⟜-intro {!!} -- this id may need to be eta expanded
      NAlg' .cons-case t   =
        ⟜-intro {k = _ ⊗ _}
        (⊗-intro (cons t) id ∘g ⊗-assoc ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)
      NAlg' .ε-cons-case t = ⟜-intro {k = _ ⊗ _}
        (⊗-intro (ε-cons t) id ∘g ⟜-app)

      N'≅⊗NFA⟨inr⟩ : recTrace _ ⊗Alg ∘g recInit _ N'Alg ≡ id
      N'≅⊗NFA⟨inr⟩ = algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
        { f = λ q → recTrace _ ⊗Alg
        ; on-nil = λ _ → refl
        ; on-cons = λ _ → refl
        ; on-ε-cons = λ _ → refl }))

      λid : AlgebraHom N (initial N) NAlg'
      λid .f q = ⟜-intro id
      λid .on-nil acc = refl
      -- the following two are true just messy
      λid .on-cons t = {!!}
      λid .on-ε-cons t = {!!}

      λrec : AlgebraHom N (initial N) NAlg'
      λrec .f q = ⟜-intro {k = _ ⊗ _}
        (recTrace _ ⊗Alg ∘g ⟜-app ∘g ⊗-intro (recTrace _ NAlg) id)
      -- the following should hold by some β/η and N'≅⊗NFA⟨inr⟩
      λrec .on-nil acc = isoFunInjective (invIso ⟜UMP) _ _
        ( (λ i → ⟜-β (recTrace ⊗NFA ⊗Alg ∘g ⟜-app ∘g ⊗-intro (recTrace N NAlg) id) i ∘g ⊗-intro (nil acc) id)
        ∙ ( λ i → recTrace ⊗NFA ⊗Alg ∘g ⟜-β ((ε-cons (N-acc _ acc) ∘g recInit _ N'Alg ∘g ⊗-unit-l)) i)
        ∙ (λ i → ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻ ∘g N'≅⊗NFA⟨inr⟩ i ∘g ⊗-unit-l)
        ∙ λ i → ⟜-β ((⊗-intro (nil acc) id)) (~ i) ∘g ⊗-unit-ll⁻ i
        )
      λrec .on-cons t = {!!}
      λrec .on-ε-cons t = {!!}

-- -- Kleene Star
module _ (N : NFA {ℓN}) where
  data *εTrans : Type ℓN where
    inr : *εTrans
    cons⟨N⟩ : ∀ {q} → ⟨ N .isAcc q .fst ⟩ → *εTrans
    N-internal : ⟨ N .ε-transition ⟩ → *εTrans

  *εTrans-rep : (Unit ⊎ ((Σ[ q ∈ _ ] ⟨ N .isAcc q .fst ⟩) ⊎ ⟨ N .ε-transition ⟩)) ≃ *εTrans
  *εTrans-rep = {!!}

  *NFA : NFA {ℓN}
  *NFA .Q = Unit ⊎ N .Q .fst , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
  *NFA .init = inl _
  *NFA .isAcc (inl _) = (Unit* , isPropUnit*) , (yes _)
  *NFA .isAcc (inr q) = (⊥* , isProp⊥*) , no lower
  *NFA .transition = N .transition
  *NFA .src = inr ∘ N .src
  *NFA .dst = inr ∘ N .dst
  *NFA .label = N .label
  *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ , isFinSetΣ (N .Q) (λ q → _ , isDecProp→isFinSet (N .isAcc q .fst .snd) (N .isAcc q .snd))) (N .ε-transition)))
  *NFA .ε-src inr = inl _
  *NFA .ε-dst inr = inr (N .init)
  *NFA .ε-src (cons⟨N⟩ {q} _) = inr q
  *NFA .ε-dst (cons⟨N⟩ {q} _) = inl _
  *NFA .ε-src (N-internal t) = inr (N .ε-src t)
  *NFA .ε-dst (N-internal t) = inr (N .ε-dst t)

  *-strong-equivalence :
    StrongEquivalence (InitParse *NFA) (KL* (InitParse N))
  *-strong-equivalence = mkStrEq
    (recInit *NFA *Alg)
    (foldKL*r (nil _) (ε-cons inr ∘g ⟜-app ∘g ⊗-intro (recInit _ NAlg) id))
    {!!}
    {!!}
    where
      *Alg : Algebra *NFA
      *Alg .the-ℓs (inl _) = _
      *Alg .the-ℓs (inr q) = _
      *Alg .G (inl _) = KL* (InitParse N)
      *Alg .G (inr q) = Parse N q ⊗ KL* (InitParse N)
      *Alg .nil-case {q = inl x} _ = KL*.nil
      *Alg .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
      *Alg .ε-cons-case inr = KL*.cons
      *Alg .ε-cons-case (cons⟨N⟩ acc) = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
      *Alg .ε-cons-case (N-internal t) = ⊗-intro (ε-cons t) id

      -- given a parse starting at q in N and a *NFA parse, make a
      -- *NFA parse starting at q.
      NAlg : Algebra N
      NAlg .the-ℓs = _
      NAlg .G q = Parse *NFA (inr q) ⊗- InitParse *NFA
      NAlg .nil-case isAcc = ⟜-intro {k = Parse _ _}
        (ε-cons (cons⟨N⟩ isAcc) ∘g ⊗-unit-l)
      NAlg .cons-case t = ⟜-intro {k = Parse _ _}
        (cons t ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)
      NAlg .ε-cons-case t = ⟜-intro {k = Parse _ _}
        (ε-cons (N-internal t) ∘g ⟜-app {h = Parse _ _})
