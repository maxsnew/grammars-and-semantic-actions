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
open import Cubical.Data.Bool
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

  litNFA≅ : StrongEquivalence (Trace literalNFA true c-st) (literal c)
  litNFA≅ =
    mkStrEq
      (rec (TraceTy literalNFA true) litAlg c-st)
      (toNFA c-st)
      the-ret
      (the-sections c-st)
    where
    ⟦_⟧st : ⟨ literalNFA .Q ⟩ → Grammar ℓ-zero
    ⟦ c-st ⟧st = literal c
    ⟦ ε-st ⟧st = ε

    litAlg : Algebra (TraceTy literalNFA true) ⟦_⟧st
    litAlg c-st = ⊕ᴰ-elim (λ { (step t _) →
      ⊗-unit-r ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      })
    litAlg ε-st = ⊕ᴰ-elim (λ { (stop _) → lowerG ∘g lowerG })

    fromNFA = rec (TraceTy literalNFA true) litAlg

    toNFA : ∀ q → ⟦ q ⟧st ⊢ Trace literalNFA true q
    toNFA c-st = STEP literalNFA _ ∘g id ,⊗ STOP literalNFA ∘g ⊗-unit-r⁻
    toNFA ε-st = STOP literalNFA

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻
      the-ret : rec (TraceTy literalNFA true) litAlg c-st ∘g toNFA c-st ≡ id
      the-ret = ⊗-unit-r⁻r

      the-sections :
        ∀ q → toNFA q ∘g fromNFA q ≡ id
      the-sections = equalizer-ind (TraceTy literalNFA true) (Trace literalNFA true)
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

-- -- Nullary Disjunction
-- module _ where
--   ⊥NFA : NFA {ℓ-zero}
--   ⊥NFA .Q = Unit , isFinSetUnit
--   ⊥NFA .init = tt
--   ⊥NFA .isAcc _ = (Empty.⊥ , isProp⊥) , no (λ z → z) -- todo: upstream this def
--   ⊥NFA .transition = Empty.⊥ , isFinSet⊥
--   ⊥NFA .ε-transition = Empty.⊥ , isFinSet⊥

--   opaque
--     unfolding AlgebraHom-seq ∃AlgebraHom
--     emptyNFA-strong-equiv :
--       StrongEquivalence (InitParse ⊥NFA) ⊥
--     emptyNFA-strong-equiv = mkStrEq
--       (recInit _ ⊥Alg)
--       ⊥-elim
--       (⊥-η _ _)
--       (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ ⊥Alg)
--         (record { f = λ _ → ⊥-elim
--                 ; on-nil = Empty.elim
--                 ; on-cons = Empty.elim
--                 ; on-ε-cons = Empty.elim })))
--       where
--         ⊥Alg : Algebra ⊥NFA
--         ⊥Alg .the-ℓs = _
--         ⊥Alg .G _ = ⊥

-- -- Binary Disjunction
-- -- Given two NFAs N and N', accepts a string if and only if
-- -- the string is accept by N or by N'
-- module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
--   data ⊕State : Type (ℓ-max ℓN ℓN') where
--     start : ⊕State
--     inl   : ⟨ N .Q ⟩  → ⊕State
--     inr   : ⟨ N' .Q ⟩ → ⊕State

--   ⊕State-rep : ⊕State ≃ (Unit ⊎ (⟨ N .Q ⟩ ⊎ ⟨ N' .Q ⟩))
--   ⊕State-rep = isoToEquiv (iso
--     (λ { start → inl tt ; (inl x) → inr (inl x) ; (inr x) → inr (inr x) })
--     (λ { (inl x) → start ; (inr (inl x)) → inl x ; (inr (inr x)) → inr x })
--     (λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl })
--     λ { start → refl ; (inl x) → refl ; (inr x) → refl })

--   ⊕Trans : FinSet (ℓ-max ℓN ℓN')
--   ⊕Trans .fst = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
--   ⊕Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

--   data ⊕εTrans : Type (ℓ-max ℓN ℓN') where
--     pick-inl : ⊕εTrans
--     pick-inr : ⊕εTrans
--     N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊕εTrans
--     N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊕εTrans

--   ⊕εTrans-rep :
--     (Unit ⊎ (Unit ⊎ (⟨ N .ε-transition ⟩ ⊎ ⟨ N' .ε-transition ⟩ ))) ≃ ⊕εTrans
--   ⊕εTrans-rep = isoToEquiv (iso
--     (λ { (inl t) → pick-inl
--     ; (inr (inl t)) → pick-inr
--     ; (inr (inr (inl t))) → N-ε-trans t
--     ; (inr (inr (inr t'))) → N'-ε-trans t' })
--     (λ { pick-inl → inl _
--     ; pick-inr → inr (inl _)
--     ; (N-ε-trans t) → inr (inr (inl t))
--     ; (N'-ε-trans t') → inr (inr (inr t')) })
--     (λ { pick-inl → refl
--     ; pick-inr → refl
--     ; (N-ε-trans t) → refl
--     ; (N'-ε-trans t') → refl })
--     (λ { (inl t) → refl
--     ; (inr (inl t)) → refl
--     ; (inr (inr (inl t))) → refl
--     ; (inr (inr (inr t'))) → refl }))

--   ⊕NFA : NFA
--   ⊕NFA .Q = ⊕State , EquivPresIsFinSet (invEquiv ⊕State-rep)
--     (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (N .Q) (N' .Q)))
--   ⊕NFA .init = start
--   ⊕NFA .isAcc = λ { start → (Empty.⊥* , isProp⊥*) , (no lower)
--     ; (inl q) → LiftDecProp'' {ℓN} {ℓN'} (N .isAcc q)
--     ; (inr q') → LiftDecProp'' {ℓN'} {ℓN} (N' .isAcc q') }
--   ⊕NFA .transition = ⊕Trans
--   ⊕NFA .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
--   ⊕NFA .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
--   ⊕NFA .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
--   ⊕NFA .ε-transition =
--     ⊕εTrans ,
--     EquivPresIsFinSet ⊕εTrans-rep
--       (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ , isFinSetUnit)
--         (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))))
--   ⊕NFA .ε-src = λ
--     { pick-inl → start ; pick-inr → start
--     ; (N-ε-trans t) → inl (N .ε-src t)
--     ; (N'-ε-trans t') → inr (N' .ε-src t') }
--   ⊕NFA .ε-dst = λ
--     { pick-inl → inl (N .init)
--     ; pick-inr → inr (N' .init)
--     ; (N-ε-trans t) → inl (N .ε-dst t)
--     ; (N'-ε-trans t') → inr (N' .ε-dst t')
--     }

--   opaque
--     unfolding _⊕_ ⊕-inr ⊕-inl AlgebraHom-seq ∃AlgebraHom
--     ⊕-strong-equivalence :
--       StrongEquivalence (InitParse ⊕NFA) (InitParse N ⊕ InitParse N')
--     ⊕-strong-equivalence = mkStrEq
--       (recInit _ ⊕Alg)
--       inj-parse
--       (⊕≡ _ _
--         (λ i → ⊕-inl ∘g N-retr i)
--         λ i → ⊕-inr ∘g N'-retr i)
--       (algebra-η ⊕NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊕Alg) (record
--         { f = λ { start → inj-parse
--                 ; (inl x) → recTrace _ NAlg
--                 ; (inr x) → recTrace _ N'Alg }
--         ; on-nil = λ { {start} → Empty.elim*
--                      ; {inl x} → λ _ → refl
--                      ; {inr x} → λ _ → refl }
--         ; on-cons = λ { (inl x) → refl ; (inr x) → refl }
--         ; on-ε-cons = λ { pick-inl → refl
--           ; pick-inr → refl
--           ; (N-ε-trans x) → refl
--           ; (N'-ε-trans x) → refl
--           } })))
--       where
--         ⊕Alg : Algebra ⊕NFA
--         ⊕Alg .the-ℓs start = (ℓ-max ℓN ℓN')
--         ⊕Alg .the-ℓs (inl _) = ℓN
--         ⊕Alg .the-ℓs (inr _) = ℓN'
--         ⊕Alg .G start = InitParse N ⊕ InitParse N'
--         ⊕Alg .G (inl q)  = Parse N q
--         ⊕Alg .G (inr q') = Parse N' q'
--         ⊕Alg .nil-case {start} ()
--         ⊕Alg .nil-case {inl x} acc  = nil (lower acc)
--         ⊕Alg .nil-case {inr x} acc' = nil (lower acc')
--         ⊕Alg .cons-case (inl t)  = cons t
--         ⊕Alg .cons-case (inr t') = cons t'
--         ⊕Alg .ε-cons-case pick-inl = ⊕-inl
--         ⊕Alg .ε-cons-case pick-inr = ⊕-inr
--         ⊕Alg .ε-cons-case (N-ε-trans t) = ε-cons t
--         ⊕Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

--         NAlg : Algebra N
--         NAlg .the-ℓs = _
--         NAlg .G q = Parse ⊕NFA (inl q)
--         NAlg .nil-case acc = nil (lift acc)
--         NAlg .cons-case t = cons (inl t)
--         NAlg .ε-cons-case t = ε-cons (N-ε-trans t)

--         N'Alg : Algebra N'
--         N'Alg .the-ℓs = _
--         N'Alg .G q = Parse ⊕NFA (inr q)
--         N'Alg .nil-case acc' = nil (lift acc')
--         N'Alg .cons-case t' = cons (inr t')
--         N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

--         inj-parse : Term (InitParse N ⊕ InitParse N') (Parse ⊕NFA start)
--         inj-parse = (⊕-elim
--           (ε-cons pick-inl ∘g recInit _ NAlg)
--           (ε-cons pick-inr ∘g recInit _ N'Alg))

--         N-retr : recTrace _ ⊕Alg ∘g recInit _ NAlg ≡ id
--         N-retr = algebra-η N (AlgebraHom-seq _ (∃AlgebraHom _ NAlg) (record
--           { f = λ q → recTrace _ ⊕Alg
--           ; on-nil = λ _ → refl
--           ; on-cons = λ _ → refl
--           ; on-ε-cons = λ _ → refl }))
--         N'-retr : recTrace _ ⊕Alg ∘g recInit _ N'Alg ≡ id
--         N'-retr = algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
--           { f = λ q → recTrace _ ⊕Alg
--           ; on-nil = λ _ → refl
--           ; on-cons = λ _ → refl
--           ; on-ε-cons = λ _ → refl
--           }))

-- -- Epsilon, the nullary sequencing
-- module _ where
--   -- an NFA with one state,
--   -- no transitions,
--   -- and the single state is both initial and accepting
--   εNFA : NFA {ℓ-zero}
--   εNFA .Q = Unit , isFinSetUnit
--   εNFA .init = tt
--   εNFA .isAcc = λ x → (Unit , isPropUnit) , (yes _)
--   εNFA .transition = Empty.⊥ , isFinSet⊥
--   εNFA .ε-transition = Empty.⊥ , isFinSet⊥

--   opaque
--     unfolding AlgebraHom-seq ∃AlgebraHom
--     εNFA-strong-equiv :
--       StrongEquivalence (InitParse εNFA) ε
--     εNFA-strong-equiv = mkStrEq
--       (recInit _ εAlg)
--       (nil _)
--       refl
--       (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ εAlg) (record
--         { f = λ _ → nil _
--         ; on-nil = λ _ → refl
--         ; on-cons = Empty.elim
--         ; on-ε-cons = Empty.elim })))
--       where
--         εAlg : Algebra εNFA
--         εAlg .the-ℓs = _
--         εAlg .G = λ _ → ε
--         εAlg .nil-case = λ _ → id

-- -- Concatenation
-- -- Given two NFAs N and N', accepts a string w if and only if
-- -- w ≡ w₁ ++ w₂ where w₁ is accepted by N and w₂ accepted by N'
-- module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
--   ⊗State : FinSet (ℓ-max ℓN ℓN')
--   ⊗State .fst = ⟨ N .Q ⟩ ⊎ ⟨ N' .Q ⟩
--   ⊗State .snd = isFinSet⊎ (N .Q) (N' .Q)

--   ⊗Trans : FinSet (ℓ-max ℓN ℓN')
--   ⊗Trans .fst = ⟨ N .transition ⟩ ⊎ ⟨ N' .transition ⟩
--   ⊗Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

--   data ⊗εTrans : Type (ℓ-max ℓN ℓN') where
--     N-acc : ∀ q → (N .isAcc q .fst .fst) → ⊗εTrans
--     N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊗εTrans
--     N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊗εTrans

--   ⊗εTrans-rep :
--     (Σ[ q ∈ ⟨ N .Q ⟩ ] (N .isAcc q .fst .fst)) ⊎
--       (⟨ N .ε-transition ⟩ ⊎ ⟨ N' .ε-transition ⟩)
--       ≃ ⊗εTrans
--   ⊗εTrans-rep = isoToEquiv (iso
--     (λ { (inl (acc)) → N-acc _ (acc .snd)
--        ; (inr (inl t)) → N-ε-trans t
--        ; (inr (inr t')) → N'-ε-trans t'})
--     (λ { (N-acc q acc) → inl (q , acc)
--        ; (N-ε-trans t) → inr (inl t)
--        ; (N'-ε-trans t') → inr (inr t') })
--     (λ { (N-acc _ _) → refl
--        ; (N-ε-trans _) → refl
--        ; (N'-ε-trans _) → refl})
--     (λ { (inl _) → refl
--        ; (inr (inl _)) → refl
--        ; (inr (inr _)) → refl }))

--   ⊗NFA : NFA
--   ⊗NFA .Q = ⊗State
--   ⊗NFA .init = inl (N .init)
--   ⊗NFA .isAcc = λ { (inl q) → (Empty.⊥* , isProp⊥*) , (no lower)
--                   ; (inr q') → LiftDecProp'' {ℓN'}{ℓN} (N' .isAcc q')}
--   ⊗NFA .transition = ⊗Trans
--   ⊗NFA .src = λ { (inl t) → inl (N .src t) ; (inr t') → inr (N' .src t') }
--   ⊗NFA .dst = λ { (inl t) → inl (N .dst t) ; (inr t') → inr (N' .dst t') }
--   ⊗NFA .label = λ { (inl t) → N .label t ; (inr t') → N' .label t' }
--   ⊗NFA .ε-transition =
--     ⊗εTrans ,
--     EquivPresIsFinSet ⊗εTrans-rep
--       (isFinSet⊎
--         (_ , isFinSetΣ (N .Q)
--           (λ q → _ ,
--             isDecProp→isFinSet (N .isAcc q .fst .snd) (N .isAcc q .snd)))
--         (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
--   ⊗NFA .ε-src = λ { (N-acc q qAcc) → inl q
--                   ; (N-ε-trans t) → inl (N .ε-src t)
--                   ; (N'-ε-trans t') → inr (N' .ε-src t') }
--   ⊗NFA .ε-dst = λ { (N-acc q qAcc) → inr (N' .init)
--                   ; (N-ε-trans t) → inl (N .ε-dst t)
--                   ; (N'-ε-trans t') → inr (N' .ε-dst t') }

--   opaque
--     unfolding AlgebraHom-seq ∃AlgebraHom recTrace P-initial !PAlgebraHom' P-idAlgebraHom
--     ⊗-strong-equivalence :
--       StrongEquivalence (InitParse ⊗NFA) (InitParse N ⊗ InitParse N')
--     ⊗-strong-equivalence = mkStrEq
--       (recInit _ ⊗Alg)
--       (P-recInit _ _ NPAlg)
--       (!PAlgebraHom' _ _ NPAlg' Prec (P-idAlgebraHom _ _ _) _)
--       (algebra-η ⊗NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊗Alg) ⊗Alg→initial))
--       where
--         ⊗Alg : Algebra ⊗NFA
--         ⊗Alg .the-ℓs (inl q) = _
--         ⊗Alg .the-ℓs (inr q') = _
--         ⊗Alg .G (inl q) = Parse N q ⊗ InitParse N'
--         ⊗Alg .G (inr q') = Parse N' q'
--         ⊗Alg .nil-case {inr q'} acc = nil (lower acc)
--         ⊗Alg .cons-case (inl t) =
--           ⊗-intro (cons t) id
--           ∘g ⊗-assoc
--         ⊗Alg .cons-case (inr t') = cons t'
--         ⊗Alg .ε-cons-case (N-acc q acc) =
--           ⊗-intro (nil acc) id
--           ∘g ⊗-unit-l⁻
--         ⊗Alg .ε-cons-case (N-ε-trans t) =
--           ⊗-intro (ε-cons t) id
--         ⊗Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

--         N'Alg : Algebra N'
--         N'Alg .the-ℓs = _
--         N'Alg .G q' = Parse ⊗NFA (inr q')
--         N'Alg .nil-case acc' = nil (lift acc')
--         N'Alg .cons-case t' = cons (inr t')
--         N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

--         NPAlg : PAlgebra N (InitParse N')
--         NPAlg .the-ℓs = _
--         NPAlg .G q = Parse ⊗NFA (inl q)
--         NPAlg .nil-case acc = ε-cons (N-acc _ acc) ∘g recInit _ N'Alg
--         NPAlg .cons-case t = cons (inl t)
--         NPAlg .ε-cons-case t = ε-cons (N-ε-trans t)

--         NPAlg' : PAlgebra N (InitParse N')
--         NPAlg' .the-ℓs = _
--         NPAlg' .G q = Parse N q ⊗ InitParse N'
--         NPAlg' .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
--         NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
--         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

--         N'≅⊗NFA⟨inr⟩ : recTrace _ ⊗Alg ∘g recInit _ N'Alg ≡ id
--         N'≅⊗NFA⟨inr⟩ =
--           algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
--             { f = λ q → recTrace _ ⊗Alg
--             ; on-nil = λ _ → refl
--             ; on-cons = λ _ → refl
--             ; on-ε-cons = λ _ → refl }))

--         ⊗Alg→initial : AlgebraHom ⊗NFA ⊗Alg (initial ⊗NFA)
--         ⊗Alg→initial .f (inl q) = P-recTrace _ _ NPAlg
--         ⊗Alg→initial .f (inr q') = recTrace _ N'Alg
--         ⊗Alg→initial .on-nil {inr q'} _ = refl
--         ⊗Alg→initial .on-cons (inl t) =
--            (λ i → ⟜-β ((cons (inl t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)) i ∘g
--              ⊗-intro (⊗-intro id (recTrace _ (underlyingAlg _ _ NPAlg))) id ∘g
--                ⊗-assoc) ∙
--             (λ i → cons (inl t) ∘g ⊗-intro id (P-recTrace _ _ NPAlg) ∘g
--               ⊗-assoc⁻∘⊗-assoc≡id i)
--         ⊗Alg→initial .on-cons (inr t) = refl
--         ⊗Alg→initial .on-ε-cons (N-acc _ acc) =
--           ((λ i →
--              ⟜-β (ε-cons (N-acc _ acc) ∘g
--                recInit _ N'Alg ∘g
--                  ⊗-unit-l) i ∘g
--                  ⊗-unit-l⁻) ∙
--           (λ i → ε-cons (N-acc _ acc) ∘g
--           recInit _ N'Alg ∘g ⊗-unit-l⁻l i))
--         ⊗Alg→initial .on-ε-cons (N-ε-trans t) =
--           (λ i → ⟜-β (ε-cons (N-ε-trans t) ∘g ⟜-app) i ∘g
--              ⊗-intro (recTrace _ (underlyingAlg _ _ NPAlg)) id)
--         ⊗Alg→initial .on-ε-cons (N'-ε-trans t') = refl

--         Prec : PAlgebraHom _ _ (P-initial N (InitParse N')) NPAlg'
--         Prec .f q =
--           recTrace ⊗NFA ⊗Alg ∘g
--           P-recTrace _ _ NPAlg
--         Prec .on-nil qAcc =
--           (λ i → recTrace _ ⊗Alg ∘g (⟜-β
--               ((ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg) ∘g ⊗-unit-l) i) ∘g
--                ⊗-unit-l⁻) ∙
--           (λ i → recTrace _ ⊗Alg ∘g
--             ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg ∘g ⊗-unit-l⁻l i) ∙
--           (λ i → ⊗-intro (nil qAcc) id ∘g ⊗-unit-l⁻ ∘g N'≅⊗NFA⟨inr⟩ i)
--         Prec .on-cons t =
--           (λ i → recTrace _ ⊗Alg ∘g
--             ⊗Alg→initial .on-cons (inl t) i)
--         Prec .on-ε-cons t =
--           (λ i → recTrace _ ⊗Alg ∘g
--             ⊗Alg→initial .on-ε-cons (N-ε-trans t) i)

--     ⊗-strong-equivalence' :
--       StrongEquivalence (InitParse ⊗NFA) (InitParse N ⊗ InitParse N')
--     ⊗-strong-equivalence' = mkStrEq
--       (recInit _ ⊗Alg)
--       (P-recInit' _ _ NPAlg)
--       (!PAlgebraHom' _ _ NPAlg' Prec (P-idAlgebraHom _ _ _) _)
--       (algebra-η ⊗NFA (AlgebraHom-seq _ (∃AlgebraHom _ ⊗Alg) ⊗Alg→initial))
--       where
--         ⊗Alg : Algebra ⊗NFA
--         ⊗Alg .the-ℓs (inl q) = _
--         ⊗Alg .the-ℓs (inr q') = _
--         ⊗Alg .G (inl q) = Parse N q ⊗ InitParse N'
--         ⊗Alg .G (inr q') = Parse N' q'
--         ⊗Alg .nil-case {inr q'} acc = nil (lower acc)
--         ⊗Alg .cons-case (inl t) =
--           ⊗-intro (cons t) id
--           ∘g ⊗-assoc
--         ⊗Alg .cons-case (inr t') = cons t'
--         ⊗Alg .ε-cons-case (N-acc q acc) =
--           ⊗-intro (nil acc) id
--           ∘g ⊗-unit-l⁻
--         ⊗Alg .ε-cons-case (N-ε-trans t) =
--           ⊗-intro (ε-cons t) id
--         ⊗Alg .ε-cons-case (N'-ε-trans t') = ε-cons t'

--         N'Alg : Algebra N'
--         N'Alg .the-ℓs = _
--         N'Alg .G q' = Parse ⊗NFA (inr q')
--         N'Alg .nil-case acc' = nil (lift acc')
--         N'Alg .cons-case t' = cons (inr t')
--         N'Alg .ε-cons-case t' = ε-cons (N'-ε-trans t')

--         NPAlg : PAlgebra N (InitParse N')
--         NPAlg .the-ℓs = _
--         NPAlg .G q = Parse ⊗NFA (inl q)
--         NPAlg .nil-case acc = ε-cons (N-acc _ acc) ∘g recInit _ N'Alg
--         NPAlg .cons-case t = cons (inl t)
--         NPAlg .ε-cons-case t = ε-cons (N-ε-trans t)

--         NPAlg' : PAlgebra N (InitParse N')
--         NPAlg' .the-ℓs = _
--         NPAlg' .G q = Parse N q ⊗ InitParse N'
--         NPAlg' .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
--         NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
--         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id
--         N'≅⊗NFA⟨inr⟩ : recTrace _ ⊗Alg ∘g recInit _ N'Alg ≡ id
--         N'≅⊗NFA⟨inr⟩ =
--           algebra-η N' (AlgebraHom-seq _ (∃AlgebraHom _ N'Alg) (record
--             { f = λ q → recTrace _ ⊗Alg
--             ; on-nil = λ _ → refl
--             ; on-cons = λ _ → refl
--             ; on-ε-cons = λ _ → refl }))
--         ⊗Alg→initial : AlgebraHom ⊗NFA ⊗Alg (initial ⊗NFA)
--         ⊗Alg→initial .f (inl q) = P-recTrace' _ _ NPAlg
--         ⊗Alg→initial .f (inr q') = recTrace _ N'Alg
--         ⊗Alg→initial .on-nil {inr q'} _ = refl
--         ⊗Alg→initial .on-cons (inl t) =
--           λ i → cons (inl t) ∘g ⊗-intro id (P-recTrace' _ _ NPAlg) ∘g
--             ⊗-assoc⁻∘⊗-assoc≡id i
--         ⊗Alg→initial .on-cons (inr t) = refl
--         ⊗Alg→initial .on-ε-cons (N-acc q x) =
--           λ i → ε-cons (N-acc q x) ∘g recTrace _ N'Alg ∘g ⊗-unit-l⁻l i
--         ⊗Alg→initial .on-ε-cons (N-ε-trans x) = refl
--         ⊗Alg→initial .on-ε-cons (N'-ε-trans x) = refl

--         Prec : PAlgebraHom _ _ (P-initial N (InitParse N')) NPAlg'
--         Prec .f q = recTrace _ ⊗Alg ∘g P-recTrace' _ _ NPAlg
--         Prec .on-nil qAcc =
--           (λ i → recTrace _ ⊗Alg ∘g
--             ε-cons (N-acc _ qAcc) ∘g recInit _ N'Alg ∘g ⊗-unit-l⁻l i) ∙
--           (λ i → ⊗-intro (nil qAcc) id ∘g ⊗-unit-l⁻ ∘g N'≅⊗NFA⟨inr⟩ i)
--         Prec .on-cons t =
--           (λ i → recTrace _ ⊗Alg ∘g ⊗Alg→initial .on-cons (inl t) i)
--         Prec .on-ε-cons t =
--           (λ i → recTrace _ ⊗Alg ∘g ⊗Alg→initial .on-ε-cons (N-ε-trans t) i)

-- -- Kleene Star
-- module _ (N : NFA {ℓN}) where
--   data *εTrans : Type ℓN where
--     inr : *εTrans
--     cons⟨N⟩ : ∀ {q} → ⟨ N .isAcc q .fst ⟩ → *εTrans
--     N-internal : ⟨ N .ε-transition ⟩ → *εTrans

--   *εTrans-rep :
--     (Unit ⊎ ((Σ[ q ∈ _ ] ⟨ N .isAcc q .fst ⟩) ⊎ ⟨ N .ε-transition ⟩)) ≃ *εTrans
--   *εTrans-rep = isoToEquiv
--     (iso
--       (λ { (inl x) → inr
--          ; (inr (inl x)) → cons⟨N⟩ (x .snd)
--          ; (inr (inr x)) → N-internal x })
--       (λ { inr → inl tt
--          ; (cons⟨N⟩ x) → inr (inl (_ , x))
--          ; (N-internal x) → inr (inr x)})
--       (λ { inr → refl ; (cons⟨N⟩ x) → refl ; (N-internal x) → refl })
--       λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl })

--   *NFA : NFA {ℓN}
--   *NFA .Q = Unit ⊎ N .Q .fst , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
--   *NFA .init = inl _
--   *NFA .isAcc (inl _) = (Unit* , isPropUnit*) , (yes _)
--   *NFA .isAcc (inr q) = (Empty.⊥* , isProp⊥*) , no lower
--   *NFA .transition = N .transition
--   *NFA .src = inr ∘ N .src
--   *NFA .dst = inr ∘ N .dst
--   *NFA .label = N .label
--   *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
--     (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ ,
--       isFinSetΣ (N .Q) (λ q → _ ,
--        isDecProp→isFinSet
--        (N .isAcc q .fst .snd) (N .isAcc q .snd))) (N .ε-transition)))
--   *NFA .ε-src inr = inl _
--   *NFA .ε-dst inr = inr (N .init)
--   *NFA .ε-src (cons⟨N⟩ {q} _) = inr q
--   *NFA .ε-dst (cons⟨N⟩ {q} _) = inl _
--   *NFA .ε-src (N-internal t) = inr (N .ε-src t)
--   *NFA .ε-dst (N-internal t) = inr (N .ε-dst t)

--   opaque
--     unfolding ⊗-unit-l⁻ ⊗-unit-l *r-initial KL*r-elim id*r-AlgebraHom AlgebraHom-seq ∃AlgebraHom recTrace P-initial !PAlgebraHom' P-idAlgebraHom
--     *-strong-equivalence :
--       StrongEquivalence (InitParse *NFA) (KL* (InitParse N))
--     *-strong-equivalence = mkStrEq
--       (recInit *NFA *Alg)
--       (foldKL*r (InitParse N) the-KL*-alg)
--       (!*r-AlgebraHom (InitParse N) (*r-initial (InitParse N))
--         (record { f = recInit *NFA *Alg ∘g foldKL*r (InitParse N) the-KL*-alg
--                 ; on-nil = refl
--                 ; on-cons = (λ i → KL*.cons ∘g
--                   nested-induction-lemma i ∘g ⊗-intro id (foldKL*r _ the-KL*-alg))
--         })
--         (id*r-AlgebraHom _ _))
--       (algebra-η *NFA (AlgebraHom-seq _ (∃AlgebraHom _ *Alg)
--         (record { f = λ {
--                     (inl _) → foldKL*r _ the-KL*-alg
--                   ; (inr q) → P-recTrace' _ _ NPAlg ∘g
--                               ⊗-intro id (foldKL*r _ the-KL*-alg) }
--                 ; on-nil = λ { {inl _} acc → refl }
--                 ; on-cons = λ { t → λ i → cons t ∘g ⊗-intro id
--                (P-recTrace' N (InitParse *NFA) NPAlg ∘g
--                  ⊗-intro id (foldKL*r (InitParse N) the-KL*-alg))
--                  ∘g ⊗-assoc⁻∘⊗-assoc≡id i }
--                 ; on-ε-cons = λ {
--                     inr → refl
--                   ; (cons⟨N⟩ x) →
--                     λ i → ε-cons (cons⟨N⟩ x) ∘g
--                       ⊗-unit-l⁻l i ∘g foldKL*r (InitParse N) the-KL*-alg
--                   ; (N-internal x) → refl } })))
--       where
--         *Alg : Algebra *NFA
--         *Alg .the-ℓs (inl _) = _
--         *Alg .the-ℓs (inr q) = _
--         *Alg .G (inl _) = KL* (InitParse N)
--         *Alg .G (inr q) = Parse N q ⊗ KL* (InitParse N)
--         *Alg .nil-case {q = inl x} _ = KL*.nil
--         *Alg .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
--         *Alg .ε-cons-case inr = KL*.cons
--         *Alg .ε-cons-case (cons⟨N⟩ acc) = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
--         *Alg .ε-cons-case (N-internal t) = ⊗-intro (ε-cons t) id

--         -- given a parse starting at q in N and a *NFA parse, make a
--         -- *NFA parse starting at q.
--         NPAlg : PAlgebra N (InitParse *NFA)
--         NPAlg .the-ℓs = _
--         NPAlg .G q = Parse *NFA (inr q)
--         NPAlg .nil-case acc = ε-cons (cons⟨N⟩ acc)
--         NPAlg .cons-case t = cons t
--         NPAlg .ε-cons-case t = ε-cons (N-internal t)

--         open *r-Algebra
--         -- NOTE : this is not an algebra for NFAs, rather for Kleene star
--         -- and is used to prove the uniqueness of the foldKL*r term
--         the-KL*-alg : *r-Algebra (InitParse N)
--         the-KL*-alg .the-ℓ = _
--         the-KL*-alg .G = InitParse *NFA
--         the-KL*-alg .nil-case = nil _
--         the-KL*-alg .cons-case = ε-cons inr ∘g P-recInit' _ _ NPAlg

--         NPAlg' : PAlgebra N (InitParse *NFA)
--         NPAlg' .the-ℓs = _
--         NPAlg' .G q = Parse N q ⊗ KL* (InitParse N)
--         NPAlg' .nil-case acc = ⊗-intro (nil acc) (recInit _ *Alg) ∘g ⊗-unit-l⁻
--         NPAlg' .cons-case t = ⊗-intro (cons t) id ∘g ⊗-assoc
--         NPAlg' .ε-cons-case t = ⊗-intro (ε-cons t) id

--         nested-induction-lemma :
--           Path (InitParse N ⊗ InitParse *NFA ⊢ InitParse N ⊗ KL* (InitParse N))
--             (recTrace *NFA *Alg ∘g P-recInit' _ _ NPAlg)
--             (⊗-intro id (recInit *NFA *Alg))
--         nested-induction-lemma =
--           !PAlgebraHom' _ _ NPAlg'
--             rec*Alg∘recInitNPAlgHom
--             recInit*AlgHom
--             _
--           where
--             rec*Alg∘recInitNPAlgHom : PAlgebraHom N (InitParse *NFA)
--               (P-initial N (InitParse *NFA))
--               NPAlg'
--             rec*Alg∘recInitNPAlgHom .f q =
--               recTrace *NFA *Alg ∘g P-recTrace' _ _ NPAlg
--             rec*Alg∘recInitNPAlgHom .on-nil acc =
--               λ i → ⊗-intro (nil acc) (recInit *NFA *Alg) ∘g
--                 ⊗-unit-ll⁻ i ∘g ⊗-unit-l⁻
--             rec*Alg∘recInitNPAlgHom .on-cons t =
--               λ i → (⊗-intro (cons t) id ∘g ⊗-assoc) ∘g
--                 ⊗-intro id (recTrace *NFA *Alg ∘g
--                   P-recTrace' N (InitParse *NFA) NPAlg) ∘g ⊗-assoc⁻∘⊗-assoc≡id i
--             rec*Alg∘recInitNPAlgHom .on-ε-cons t = refl

--             recInit*AlgHom :
--               PAlgebraHom N
--                 (InitParse *NFA) (P-initial N (InitParse *NFA)) NPAlg'
--             recInit*AlgHom .f q = ⊗-intro id (recTrace _ *Alg)
--             recInit*AlgHom .on-nil acc = refl
--             recInit*AlgHom .on-cons t = refl
--             recInit*AlgHom .on-ε-cons t = refl
