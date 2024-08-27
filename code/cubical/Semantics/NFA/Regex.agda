open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.NFA.Regex ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

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
open import Cubical.Data.SumFin
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
  STATE≅Fin2 .Iso.fun ε-st = fsuc fzero
  STATE≅Fin2 .Iso.inv fzero = c-st
  STATE≅Fin2 .Iso.inv (fsuc x) = ε-st
  STATE≅Fin2 .Iso.rightInv fzero = refl
  STATE≅Fin2 .Iso.rightInv (fsuc fzero) = refl
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

      open Algebra
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
      open Algebra
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
    inl   : N .Q .fst  → ⊕State
    inr   : N' .Q .fst → ⊕State

  ⊕Trans = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
  data ⊕εTrans : Type (ℓ-max ℓN ℓN') where
    pick-inl : ⊕εTrans
    pick-inr : ⊕εTrans
    N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊕εTrans
    N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊕εTrans

  isSet⊕State : isSet ⊕State
  isSet⊕State = {!!}

  ⊕NFA' : NFA
  ⊕NFA' .Q = ⊕State , {!!}
  ⊕NFA' .init = start
  ⊕NFA' .isAcc = λ { start → (⊥* , isProp⊥*) , (no lower)
    ; (inl x) → LiftDecProp'' {ℓN} {ℓN'} (N .isAcc x)
    ; (inr x) → LiftDecProp'' {ℓN'} {ℓN} (N' .isAcc x) }
  ⊕NFA' .transition = ⊕Trans , (isFinSet⊎ (N .transition) (N' .transition))
  ⊕NFA' .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
  ⊕NFA' .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
  ⊕NFA' .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
  ⊕NFA' .ε-transition = ⊕εTrans , {!!}
  ⊕NFA' .ε-src = λ
    { pick-inl → start ; pick-inr → start
    ; (N-ε-trans t) → inl (N .ε-src t)
    ; (N'-ε-trans t') → inr (N' .ε-src t') }
  ⊕NFA' .ε-dst = λ
    { pick-inl → inl (N .init)
    ; pick-inr → inr (N' .init)
    ; (N-ε-trans t) → inl (N .ε-dst t)
    ; (N'-ε-trans t') → inr (N' .ε-dst t')
    }

  ⊕-strong-equivalence :
    StrongEquivalence (InitParse ⊕NFA') (InitParse N ⊕ InitParse N')
  ⊕-strong-equivalence = mkStrEq
    (recInit _ ⊕Alg)
    inj-parse
    (⊕≡ _ _
      (λ i → ⊕-inl ∘g N-retr i)
      λ i → ⊕-inr ∘g N'-retr i)
    (algebra-η ⊕NFA' (AlgebraHom-seq _ (∃AlgebraHom _ ⊕Alg) (record
      { f = λ { start → inj-parse
              ; (inl x) → recTrace _ NAlg
              ; (inr x) → recTrace _ N'Alg }
      ; on-nil = λ { {start} → ⊥.elim* ; {inl x} → λ _ → refl ; {inr x} → λ _ → refl }
      ; on-cons = λ { (inl x) → refl ; (fsuc x) → refl }
      ; on-ε-cons = λ { pick-inl → refl
        ; pick-inr → refl
        ; (N-ε-trans x) → refl
        ; (N'-ε-trans x) → refl
        } })))
    where
      open Algebra
      ⊕Alg : Algebra ⊕NFA'
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
      NAlg .G q = Parse ⊕NFA' (inl q)
      NAlg .nil-case acc = nil (lift acc)
      NAlg .cons-case t = cons (inl t)
      NAlg .ε-cons-case t = ε-cons (N-ε-trans t)

      N'Alg : Algebra N'
      N'Alg .the-ℓs = _
      N'Alg .G q = Parse ⊕NFA' (inr q)
      N'Alg .nil-case acc' = nil (lift acc')
      N'Alg .cons-case t' = cons (inr t')
      N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

      inj-parse : Term (InitParse N ⊕ InitParse N') (Parse ⊕NFA' start)
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
      open Algebra
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
  -- Has the states from N and the states from N'
  -- the initial state of the subautomaton N is the initial state
  -- Every accepting state of N has an epsilon transiton to
  -- the initial state of N'
  -- The accepting states of the subautomaton N' are accepting
  ⊗NFA : NFA {ℓ-max ℓN ℓN'}
  Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
  Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
  init ⊗NFA = inl (N .init)
  isAcc ⊗NFA (inl x) =
    DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
  isAcc ⊗NFA (inr x) =
    LiftDecProp {ℓN'}{ℓN} (N' .isAcc x)
  transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
  transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
  -- transitions from subautomata
  src ⊗NFA (inl x) = inl (N .src x)
  dst ⊗NFA (inl x) = inl (N .dst x)
  src ⊗NFA (inr x) = inr (N' .src x)
  dst ⊗NFA (inr x) = inr (N' .dst x)
  label ⊗NFA (inl x) = N .label x
  label ⊗NFA (inr x) = N' .label x
  ε-transition ⊗NFA .fst =
    (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
    (N .ε-transition .fst ⊎ N' .ε-transition .fst)
  ε-transition ⊗NFA .snd =
    isFinSet⊎
      (_ , isFinSetΣ (N .Q)
        λ x → _ ,
          isDecProp→isFinSet
            (N .isAcc x .fst .snd)
            (N .isAcc x .snd))
      ((_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
  -- ε-transition from accepting states of N to initial state of N'
  ε-src ⊗NFA (inl x) = inl (x .fst)
  ε-dst ⊗NFA (inl x) = inr (N' .init)
  -- ε-transitions from subautomata
  ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
  ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
  ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
  ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

  open Algebra
  open AlgebraHom

  private
    the-N'-alg : Algebra N'
    the-ℓs the-N'-alg _ = ℓ-max ℓN ℓN'
    G the-N'-alg q = Parse ⊗NFA (inr q)
    nil-case the-N'-alg qAcc =
      nil (LiftDecPropWitness (N' .isAcc _) qAcc)
    cons-case the-N'-alg tr = cons (inr tr)
    ε-cons-case the-N'-alg εtr = ε-cons (inr (inr εtr))

    initialN'→the-N'-alg : AlgebraHom N' (initial N') the-N'-alg
    initialN'→the-N'-alg = ∃AlgebraHom N' the-N'-alg

    the-N-alg : Algebra N
    the-ℓs the-N-alg _ = ℓ-max ℓN ℓN'
    G the-N-alg q = Parse ⊗NFA (inl q) ⊗- Parse N' (N' .init)
    nil-case the-N-alg {q} qAcc =
      ⊗--intro
        (⊗-unit-l ⋆
        (initialN'→the-N'-alg .f (N' .init) ⋆
        ε-cons (inl (q , qAcc))))
    cons-case the-N-alg tr =
      ⊗--assoc {h = Parse ⊗NFA (inl (N .dst tr))} ⋆
      (functoriality
        {g = literal (N .label tr) ⊗ Parse ⊗NFA (inl (N .dst tr))}
        {h = Parse ⊗NFA (inl (N .src tr))}
        (var ⊗-func Parse N' (N' .init))
        (cons (inl tr)))
    ε-cons-case the-N-alg εtr =
      (functoriality
        {g = Parse ⊗NFA (inl (N .ε-dst εtr))}
        {h = Parse ⊗NFA (inl (N .ε-src εtr))}
        (var ⊗-func Parse N' (N' .init))
        (ε-cons (inr (inl εtr))))

    initialN→the-N-alg : AlgebraHom N (initial N) the-N-alg
    initialN→the-N-alg = ∃AlgebraHom N the-N-alg

    the-⊗NFA-alg : Algebra ⊗NFA
    the-ℓs the-⊗NFA-alg (inl q) = ℓ-max ℓN ℓN'
    the-ℓs the-⊗NFA-alg (inr q) = ℓN'
    G the-⊗NFA-alg (inl q) = Parse N q ⊗ Parse N' (N' .init)
    G the-⊗NFA-alg (inr q) = Parse N' q
    nil-case the-⊗NFA-alg {inl q} qAcc = ⊥.rec (lower qAcc)
    nil-case the-⊗NFA-alg {inr q} qAcc =
      nil (LowerDecPropWitness (N' .isAcc q) qAcc)
    cons-case the-⊗NFA-alg (inl tr) =
      ⊗-assoc ⋆
      functoriality (var ⊗l Parse N' (N' .init))
        (cons tr)
    cons-case the-⊗NFA-alg (inr tr) = cons tr
    ε-cons-case the-⊗NFA-alg (inl N-acc) =
      ⊗-unit-l⁻ ⋆
      ⊗-intro (nil (N-acc .snd)) id
    ε-cons-case the-⊗NFA-alg (inr (inl εtr)) =
      functoriality (var ⊗l Parse N' (N' .init))
        (ε-cons εtr)
    ε-cons-case the-⊗NFA-alg (inr (inr εtr)) = ε-cons εtr

    initial⊗NFA→the-⊗NFA-alg :
      AlgebraHom ⊗NFA (initial ⊗NFA) the-⊗NFA-alg
    initial⊗NFA→the-⊗NFA-alg = ∃AlgebraHom ⊗NFA the-⊗NFA-alg

    the-N'-alg→initialN' : AlgebraHom N' the-N'-alg (initial N')
    f the-N'-alg→initialN' q = initial⊗NFA→the-⊗NFA-alg .f (inr q)
    on-nil the-N'-alg→initialN' {q} qAcc =
      cong nil (LowerLiftWitness (N' .isAcc q) qAcc)
    on-cons the-N'-alg→initialN' tr = refl
    on-ε-cons the-N'-alg→initialN' εtr = refl

    the-N-alg→initialN : AlgebraHom N the-N-alg (initial N)
    f the-N-alg→initialN q =
      -- {!!}
      -- functoriality (var ⊗-func Parse N' (N' .init))
      --   (initial⊗NFA→the-⊗NFA-alg .f (inl q)) ⋆
      -- {!!}
      {!initial⊗NFA→the-⊗NFA-alg .f (inl q)!}
    on-nil the-N-alg→initialN = {!!}
    on-cons the-N-alg→initialN = {!!}
    on-ε-cons the-N-alg→initialN = {!!}

    the-⊗NFA-alg→initial⊗NFA :
      AlgebraHom ⊗NFA the-⊗NFA-alg (initial ⊗NFA)
    f the-⊗NFA-alg→initial⊗NFA (inl q) =
      ⊗-intro
        (initialN→the-N-alg .f q) id ⋆
      ⊗--app
    f the-⊗NFA-alg→initial⊗NFA (inr q) = initialN'→the-N'-alg .f q
    on-nil the-⊗NFA-alg→initial⊗NFA {inr q} qAcc =
      cong nil (LiftLowerWitness (N' .isAcc q) qAcc)
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.cons-case (inl tr))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.src ⊗NFA (inl tr)))
--       ≡
--       seq
--       (⊗-intro id
--        (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--         (Semantics.NFA.Base.NFA.dst ⊗NFA (inl tr))))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.cons-case (inl tr))
    on-cons the-⊗NFA-alg→initial⊗NFA (inl tr) = {!!}
    on-cons the-⊗NFA-alg→initial⊗NFA (inr tr) = refl
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (inl N-acc))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-src ⊗NFA (inl N-acc)))
--       ≡
--       seq
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-dst ⊗NFA (inl N-acc)))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (inl N-acc))
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inl N-acc) = {!!}
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (fsuc (inl εtr)))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-src ⊗NFA (fsuc (inl εtr))))
--       ≡
--       seq
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-dst ⊗NFA (fsuc (inl εtr))))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (fsuc (inl εtr)))
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inl εtr)) = {!!}
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inr εtr)) = refl

  open Iso
  ⊗NFA-strong-equiv :
    isStronglyEquivalent
      (Parse ⊗NFA (⊗NFA .init))
      ((Parse N (N .init)) ⊗ (Parse N' (N' .init)))
  fun (⊗NFA-strong-equiv w) = initial⊗NFA→the-⊗NFA-alg .f (⊗NFA .init) w
  inv (⊗NFA-strong-equiv w) = the-⊗NFA-alg→initial⊗NFA .f (inl (N .init)) w
  rightInv (⊗NFA-strong-equiv w) p⊗ =
    {!!}
  leftInv (⊗NFA-strong-equiv w) p =
    cong (λ a → a w p)
      (initial→initial≡id ⊗NFA
        (AlgebraHom-seq ⊗NFA
          initial⊗NFA→the-⊗NFA-alg
          the-⊗NFA-alg→initial⊗NFA)
        (inl (N .init)))

-- Kleene Star
module _ (N : NFA {ℓN}) where
  KL*NFA : NFA {ℓN}
  Q KL*NFA .fst = N .Q .fst ⊎ ⊤
  Q KL*NFA .snd = isFinSet⊎ (N .Q) (_ , isFinSetUnit)
  init KL*NFA = inl (N .init)
  isAcc KL*NFA (inl x) =
    DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
  isAcc KL*NFA (inr x) =
    DecPropIso .Iso.inv (Unit* , (true , (invEquiv LiftEquiv)))
  transition KL*NFA = N .transition
  src KL*NFA x = inl (N .src x)
  dst KL*NFA x = inl (N .dst x)
  label KL*NFA = N .label
  ε-transition KL*NFA .fst =
    ⊤ ⊎
    ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
      (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst))
  ε-transition KL*NFA .snd =
    isFinSet⊎
      (_ , isFinSetUnit)
      (_ , isFinSet⊎
        (_ , isFinSetAccΣ)
        (_ , isFinSetAccΣ))
    where
    isFinSetAccΣ :
      isFinSet
        (Σ-syntax (N .Q .fst) (λ q → N .isAcc q .fst .fst))
    isFinSetAccΣ =
      isFinSetΣ (N .Q)
        (λ x → _ ,
          isDecProp→isFinSet
            (N .isAcc x .fst .snd)
            (N .isAcc x .snd))
  ε-src KL*NFA (inl x) = inl (N .init)
  ε-dst KL*NFA (inl x) = inr _
  ε-src KL*NFA (inr (inl x)) = inl (x .fst)
  ε-dst KL*NFA (inr (inl x)) = inl (N .init)
  ε-src KL*NFA (inr (inr x)) = inl (x .fst)
  ε-dst KL*NFA (inr (inr x)) = inr _

  open Algebra
  open AlgebraHom

  private
    the-N-alg : Algebra N
    the-N-alg = {!!}

    initialN→the-N-alg : AlgebraHom N (initial N) the-N-alg
    initialN→the-N-alg = ∃AlgebraHom N the-N-alg

    the-KL*-alg : Algebra KL*NFA
    the-KL*-alg = {!!}

    initialKL*→the-KL*-alg : AlgebraHom KL*NFA (initial KL*NFA) the-KL*-alg
    initialKL*→the-KL*-alg = ∃AlgebraHom KL*NFA the-KL*-alg
