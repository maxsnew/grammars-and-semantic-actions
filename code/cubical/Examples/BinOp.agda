{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat as Nat
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

data Tok : Type where
  [ ] : Tok     -- parens
  * : Tok       -- the binary operation
  num : ℕ → Tok -- constants

open Iso
opaque
  TokRep : Iso Tok (Bool ⊎ (Unit ⊎ ℕ))
  TokRep =
      iso
        (λ { [ → inl true ; ] → inl false ; * → inr (inl _) ; (num x) → inr (inr x)})
        (λ { (inl false) → ] ; (inl true) → [ ; (inr (inl x)) → * ; (inr (inr x)) → num x})
        (λ { (inl false) → refl ; (inl true) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl})
        λ { [ → refl ; ] → refl ; * → refl ; (num x) → refl}

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .leftInv)
      (isSet⊎ isSetBool (isSet⊎ isSetUnit isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

anyNum : Grammar _
anyNum = ⊕[ n ∈ ℕ ] ＂ num n ＂

{--
-- Context-free grammar of expressions with binary operation *
-- over natural numbers and parentheses
--
-- S → E
-- E → A | A * E
-- A → n | [ E ]
--
--}
module LL⟨1⟩ where
  -- the nonterminal grammars
  data Nonterminal : Type ℓ-zero where
    Exp Atom : Nonterminal

  -- the constructor names of each nonterminal
  data Tag : (N : Nonterminal) → Type ℓ-zero where
    done add : Tag Exp
    num parens : Tag Atom

  BinOpTy : Nonterminal → Functor Nonterminal
  BinOpTy Exp =
    ⊕e (Tag Exp)
      λ where
        done → Var Atom
        add → Var Atom ⊗e k ＂ * ＂ ⊗e Var Exp
  BinOpTy Atom =
    ⊕e (Tag Atom)
      λ where
        num → k anyNum
        parens → k ＂ [ ＂ ⊗e Var Exp ⊗e k ＂ ] ＂

  BinOpG : Nonterminal → Grammar ℓ-zero
  BinOpG = μ BinOpTy

  EXP = BinOpG Exp
  ATOM = BinOpG Atom

  DONE : ATOM ⊢ EXP
  DONE = roll ∘g ⊕ᴰ-in done ∘g liftG

  ADD : ATOM ⊗ ＂ * ＂ ⊗ EXP ⊢ EXP
  ADD = roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG ,⊗ liftG

  NUM : anyNum ⊢ ATOM
  NUM = roll ∘g ⊕ᴰ-in num ∘g liftG

  PARENS : ＂ [ ＂ ⊗ EXP ⊗ ＂ ] ＂ ⊢ ATOM
  PARENS = roll ∘g ⊕ᴰ-in parens ∘g liftG ,⊗ liftG ,⊗ liftG

module Automaton where
  data AutomatonState : Type ℓ-zero where
    Opening DoneOpening Closing Multiplying : AutomatonState

  -- the constructor names of each automaton state
  data AutomatonTag (b : Bool) (n : ℕ) : (N : AutomatonState) → Type ℓ-zero where
    left num : AutomatonTag b n Opening
    doneO unexpected*O unexpected]O  : b Eq.≡ false → AutomatonTag b n Opening
    lookaheadRP lookaheadNot : AutomatonTag b n DoneOpening
    closeGood : ∀ n-1 → n Eq.≡ suc n-1 → AutomatonTag b n Closing
    closeBad : n Eq.≡ 0 → AutomatonTag b n Closing
    doneC unexpected[C unexpected*C unexpectedNumC : b Eq.≡ false → AutomatonTag b n Closing
    doneGood : n Eq.≡ 0 → b Eq.≡ true → AutomatonTag b n Multiplying
    add : AutomatonTag b n Multiplying
    doneBad unexpected[M unexpected]M unexpectedNumM : b Eq.≡ false → AutomatonTag b n Multiplying

  AutomatonTy : Bool → ℕ → AutomatonState → Functor (ℕ × AutomatonState)
  AutomatonTy b n Opening =
    ⊕e (AutomatonTag b n Opening)
      λ where
        left → k ＂ [ ＂ ⊗e Var (suc n , Opening)
        num → k anyNum ⊗e Var (n , DoneOpening)
        (doneO Eq.refl) → k ε
        (unexpected]O Eq.refl) → k ＂ ] ＂ ⊗e k ⊤
        (unexpected*O Eq.refl) → k ＂ * ＂ ⊗e k ⊤
  AutomatonTy b n DoneOpening =
    ⊕e (AutomatonTag b n DoneOpening)
      λ where
        lookaheadRP →
          &e Bool -- binary product
            λ where
              true → k ＂ ] ＂ ⊗e k ⊤
              false → Var (n , Closing)
        lookaheadNot →
          &e Bool -- binary product
            λ where
              true →
                -- NotStartsWithRP = ε ⊕ (＂ [ ＂ ⊕ ＂ * ＂ ⊕ anyNum) ⊗ ⊤
                ⊕e Bool -- binary coproduct
                  λ where
                    true → k ε
                    false →
                      (⊕e Bool
                        λ where
                          true → k ＂ [ ＂
                          false →
                            ⊕e Bool
                              λ where
                                true → k ＂ * ＂
                                false → k anyNum) ⊗e k ⊤
              false → Var (n , Multiplying)
  AutomatonTy b n Closing =
    ⊕e (AutomatonTag b n Closing)
      λ where
        (closeGood n-1 Eq.refl) → k ＂ ] ＂ ⊗e Var (n-1 , DoneOpening)
        (closeBad Eq.refl) → k ＂ ] ＂
        (doneC Eq.refl) → k ε
        (unexpected[C Eq.refl) → k ＂ [ ＂ ⊗e k ⊤
        (unexpected*C Eq.refl) → k ＂ * ＂ ⊗e k ⊤
        (unexpectedNumC Eq.refl) → k anyNum ⊗e k ⊤
  AutomatonTy b n Multiplying =
    ⊕e (AutomatonTag b n Multiplying)
      λ where
        (doneGood Eq.refl Eq.refl) → k ε
        (doneBad Eq.refl) → k ε
        add → k ＂ [ ＂ ⊗e Var (n , Opening)
        (unexpected[M Eq.refl) → k ＂ [ ＂ ⊗e k ⊤
        (unexpected]M Eq.refl) → k ＂ ] ＂ ⊗e k ⊤
        (unexpectedNumM Eq.refl) → k anyNum ⊗e k ⊤

  AutomatonG : Bool → ℕ → AutomatonState → Grammar ℓ-zero
  AutomatonG b n S = μ (λ (n' , s') → AutomatonTy b n' s') (n , S)

  -- NotStartsWithRP = ε ⊕ (＂ [ ＂ ⊕ ＂ * ＂ ⊕ anyNum) ⊗ ⊤
  NOT_STARTS_WITH_[ : Grammar ℓ-zero
  NOT_STARTS_WITH_[ = ε ⊕ (＂ [ ＂ ⊕ ＂ * ＂ ⊕ anyNum) ⊗ ⊤

  -- States of the automaton as Grammars

  -- Opening: at the start of an expression, the term starts with a
  -- sequence of 0 or more opening parens, which we count. Ends when
  -- we see a number, then we use lookahead to determine whether to
  -- parse closing parens or start parsing a multiplication sequence
  OPENING : Bool → ℕ → Grammar ℓ-zero
  OPENING b n = AutomatonG b n Opening

  DONE_OPENING : Bool → ℕ → Grammar ℓ-zero
  DONE_OPENING b n = AutomatonG b n DoneOpening

  -- Closing: parse as many closing parens as you can, eventually
  -- use lookahead to decide when to start parsing multiplication sequence
  CLOSING : Bool → ℕ → Grammar ℓ-zero
  CLOSING b n = AutomatonG b n Closing

  MULTIPLYING : Bool → ℕ → Grammar ℓ-zero
  MULTIPLYING b n = AutomatonG b n Multiplying

  -- Constructors of the automaton states that adjust for lifts
  LEFT : ∀ n b → ＂ [ ＂ ⊗ OPENING b (suc n) ⊢ OPENING b n
  LEFT n b = roll ∘g ⊕ᴰ-in left ∘g liftG ,⊗ liftG

  NUM : ∀ n b → anyNum ⊗ DONE_OPENING b n ⊢ OPENING b n
  NUM n b = roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ liftG

  DONE_O : ∀ n → ε ⊢ OPENING false n
  DONE_O n = roll ∘g ⊕ᴰ-in (doneO Eq.refl) ∘g liftG

  UNEXPECTED*O : ∀ n → ＂ * ＂ ⊗ ⊤ ⊢ OPENING false n
  UNEXPECTED*O n = roll ∘g ⊕ᴰ-in (unexpected*O Eq.refl) ∘g liftG ,⊗ liftG

  UNEXPECTED]O : ∀ n → ＂ ] ＂ ⊗ ⊤ ⊢ OPENING false n
  UNEXPECTED]O n = roll ∘g ⊕ᴰ-in (unexpected]O Eq.refl) ∘g liftG ,⊗ liftG

  -- TODO : go between binary sum/product and there inductive counterparts
  -- this is in each of Grammar.Sum/Grammar.Product
  LOOKAHEAD_RP  : ∀ n b → (＂ ] ＂ ⊗ ⊤) & CLOSING b n ⊢ DONE_OPENING b n
  LOOKAHEAD_RP n b = roll ∘g ⊕ᴰ-in lookaheadRP ∘g {!!}

  LOOKAHEAD_NOT : ∀ n b → NOT_STARTS_WITH_[ & MULTIPLYING b n ⊢ DONE_OPENING b n
  LOOKAHEAD_NOT n b = roll ∘g ⊕ᴰ-in lookaheadNot ∘g {!!}

  CLOSE_GOOD : ∀ n b → ＂ ] ＂ ⊗ DONE_OPENING b n ⊢ CLOSING b (suc n)
  CLOSE_GOOD n b = roll ∘g ⊕ᴰ-in (closeGood n Eq.refl) ∘g liftG ,⊗ liftG

  CLOSE_BAD : ∀ b → ＂ ] ＂ ⊢ CLOSING b 0
  CLOSE_BAD b = roll ∘g ⊕ᴰ-in (closeBad Eq.refl) ∘g liftG

  DONE_C : ∀ n → ε ⊢ CLOSING false n
  DONE_C n = roll ∘g ⊕ᴰ-in (doneC Eq.refl) ∘g liftG

  UNEXPECTED[C : ∀ n → ＂ [ ＂ ⊗ ⊤ ⊢ CLOSING false n
  UNEXPECTED[C n = roll ∘g ⊕ᴰ-in (unexpected[C Eq.refl) ∘g liftG ,⊗ liftG

  UNEXPECTED*C  : ∀ n → ＂ * ＂ ⊗ ⊤ ⊢ CLOSING false n
  UNEXPECTED*C n = roll ∘g ⊕ᴰ-in (unexpected*C Eq.refl) ∘g liftG ,⊗ liftG

  UNEXPECTED_NUM_C : ∀ n → anyNum ⊗ ⊤ ⊢ CLOSING false n
  UNEXPECTED_NUM_C n = roll ∘g ⊕ᴰ-in (unexpectedNumC Eq.refl) ∘g liftG ,⊗ liftG

  DONE_GOOD : ε ⊢ MULTIPLYING true 0
  DONE_GOOD = roll ∘g ⊕ᴰ-in (doneGood Eq.refl Eq.refl) ∘g liftG

  ADD : ∀ n b → ＂ [ ＂ ⊗ OPENING b n ⊢ MULTIPLYING b n
  ADD n b = roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG

  DONE_BAD : ∀ n → ε ⊢ MULTIPLYING false (suc n)
  DONE_BAD n = roll ∘g ⊕ᴰ-in (doneBad Eq.refl) ∘g liftG

  UNEXPECTED[M : ∀ n → ＂ [ ＂ ⊗ ⊤ ⊢ MULTIPLYING false n
  UNEXPECTED[M n = roll ∘g ⊕ᴰ-in (unexpected[M Eq.refl) ∘g liftG ,⊗ liftG

  UNEXPECTED]M : ∀ n → ＂ ] ＂ ⊗ ⊤ ⊢ MULTIPLYING false n
  UNEXPECTED]M n = roll ∘g ⊕ᴰ-in (unexpected]M Eq.refl) ∘g liftG ,⊗ liftG

  UNEXPECTED_NUM_M : ∀ n → anyNum ⊗ ⊤ ⊢ MULTIPLYING false n
  UNEXPECTED_NUM_M n = roll ∘g ⊕ᴰ-in (unexpectedNumM Eq.refl) ∘g liftG ,⊗ liftG

--   record Algebra ℓ : Type (ℓ-suc ℓ) where
--     field
--       UO : ℕ → Grammar ℓ
--       UC : ℕ → Grammar ℓ
--       UM : ℕ → Grammar ℓ
--     UDO : ℕ → Grammar ℓ
--     UDO n = ((ε ⊕ (literal * ⊕ literal LP ⊕ anyNum) ⊗ ⊤) & UM n)
--       ⊕ ((literal RP ⊗ ⊤) & UC n)
--     field
--       [left] : ∀ {n} → literal LP ⊗ UO (suc n) ⊢ UO n
--       [num]  : ∀ {n} → (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ UDO n ⊢ UO n
--       [rightClose] : ∀ {n} → literal RP ⊗ UDO n ⊢ UC (suc n)
--       [done] : ε ⊢ UM 0
--       [times] : ∀ {n} → literal * ⊗ UO n ⊢ UM n

--   open Algebra
--   opaque
--     unfolding _⊗_ _⊕_ _&_
--     initialAlgebra : Algebra ℓ-zero
--     initialAlgebra .UO n = Opening n true
--     initialAlgebra .UC n = Closing n true
--     initialAlgebra .UM n = Multiplying n true
--     initialAlgebra .[left] = left
--     initialAlgebra .[num] = num
--     initialAlgebra .[rightClose] = rightClose
--     initialAlgebra .[times] = times
--     initialAlgebra .[done] = done

--   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
--     field
--       fO : ∀ n → A .UO n ⊢ B .UO n
--       fC : ∀ n → A .UC n ⊢ B .UC n
--       fM : ∀ n → A .UM n ⊢ B .UM n
--       -- TODO: the equations

--   opaque
--     unfolding _⊗_ _⊕_ _&_ initialAlgebra
--     -- TODO these defs need indexed pattern matching
--     fold : ∀ {ℓ} (A : Algebra ℓ) → Hom initialAlgebra A
--     fold A = record { fO = rO ; fC = rC ; fM = rM } where
--       rO : ∀ n → Opening n true ⊢ A .UO n
--       rC : ∀ n → Closing n true ⊢ A .UC n
--       rM : ∀ n → Multiplying n true ⊢ A .UM n
--       rDO : ∀ n → DoneOpening n true ⊢ UDO A n
--       rO n w (left _ (sp , lp , o)) = A .[left] w (sp , (lp , rO _ _ o))
--       rO n w (num _ (sp , m , doo)) = A .[num] _ (sp , m , rDO _ _ doo)
--       rC _ w (rightClose _ (sp , rp , doo)) = A .[rightClose] _ (sp , rp , rDO _ _ doo)
--       rM _ w (done _ x) = A .[done] _ x
--       rM _ w (times _ (sp , star , o)) = A .[times] _ (sp , star , rO _ _ o)
--       rDO n w (inl x) = inl ((x .fst) , (rM _ _ (x .snd)))
--       rDO n w (inr x) = inr (x .fst , rC _ _ (x .snd))
--     Peek : Maybe Tok → Grammar ℓ-zero
--     Peek = Maybe.rec ε (λ c → literal c ⊗ ⊤)

--     Goal : Grammar ℓ-zero
--     Goal = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
--       (LinearΣ (Opening n)
--       & LinearΣ (Closing n)
--       & LinearΣ (Multiplying n))

--     -- TODO typechecking this parse term is very slow
--     -- Should probably split it into several pieces
-- --     opaque
-- --       -- unfolding LL⟨1⟩.fold LL⟨1⟩.num' LL⟨1⟩.parens' LL⟨1⟩.initialAlgebra _⊗_ _⊕_ _&_ _⇒_ ⊕-elim ⇒-intro ⇐-intro ⟜-intro ⟜-app ⊸-intro ⊸-app KL*r-elim fold initialAlgebra ⊗-intro &-intro &-π₁ &-π₂ ⊕-inl ⊕-inr ⇒-app
-- --       parse' : string ⊢ LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- --         (LinearΣ (Opening n)
-- --         & LinearΣ (Closing n)
-- --         & LinearΣ (Multiplying n))
-- --       parse' = foldKL*r char
-- --         (record {
-- --           the-ℓ = ℓ-zero
-- --         ; G = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- --               (LinearΣ (Opening n)
-- --               & LinearΣ (Closing n)
-- --               & LinearΣ (Multiplying n))
-- --         ; nil-case =
-- --           LinΣ-intro Maybe.nothing
-- --           ,& LinΠ-intro λ n →
-- --             (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --             ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --             ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- --         ; cons-case =
-- --           (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- --             (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- --           ,& LinΠ-intro λ n →
-- --             {!!}
-- --         })
-- --       -- foldKL*r _ (record { the-ℓ = _ ; G = _
-- --       --   ; nil-case =
-- --       --     LinΣ-intro Maybe.nothing
-- --       --     ,& LinΠ-intro λ n →
-- --       --     (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --       --     ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --       --     ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- --       --   ; cons-case =
-- --       --     (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- --       --       (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- --       --     ,& LinΠ-intro λ n →
-- --       --       (⊸-intro⁻
-- --       --         (LinΣ-elim λ
-- --       --         { (num x) → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --           -- goto closing
-- --       --           { (just RP) → ⇒-intro (⇐-intro⁻ (((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ ⊕-inr))) ∘g &-π₁) ∘g &-π₂))
-- --       --           ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just (num y)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro y) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           }))
-- --       --           ∘g id ,⊗ id ,&p LinΠ-app n)
-- --       --           --  (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --         ; LP → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (((LinΣ-elim (λ b → ⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g left)) ∘g &-π₁)) ∘g LinΠ-app (suc n) ∘g &-π₂))
-- --       --         ; RP → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --         ; * → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inr ,⊗ ⊤-intro)
-- --       --         })
-- --       --       )
-- --       --       -- ⊸-intro⁻
-- --       --       ,& ⊸-intro⁻ (LinΣ-elim λ
-- --       --        { RP → ⊸-intro {k = LinearΣ (Closing n)} (Nat.elim {A = λ n → Term (literal RP ⊗ Goal) (LinearΣ (Closing n))}
-- --       --          -- empty stack
-- --       --          (LinΣ-intro false ∘g rightUnmatched ∘g id ,⊗ ⊤-intro)
-- --       --          -- popped
-- --       --          (λ n-1 _ → (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --            { (just RP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ ⊕-inr))) ∘g &-π₁ ∘g &-π₂))
-- --       --            ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just (num x)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            })) ∘g id ,⊗ id ,&p LinΠ-app n-1))
-- --       --          n)
-- --       --        ; LP → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- --       --        ; * → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro)
-- --       --        })
-- --       --       ,&
-- --       --      (⊸-intro⁻ (LinΣ-elim λ
-- --       --        { * → ⊸-intro {k = LinearΣ (Multiplying n)} (⟜-intro⁻ ((((LinΣ-elim λ b → ⟜-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro b ∘g times)) ∘g &-π₁) ∘g LinΠ-app n) ∘g &-π₂))
-- --       --        ; LP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --        ; RP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro) }))
-- --       --   })

-- -- --     parse : string ⊢ LinΣ[ b ∈ Bool ] Opening zero b
-- -- --     parse = ((&-π₁ ∘g LinΠ-app zero) ∘g &-π₂) ∘g parse'

-- -- -- -- Soundness: i.e., that from every trace we can extract an LL(1) parse
-- -- -- module Soundness where
-- -- --   buildExp : Automaton.Opening 0 true ⊢ LL⟨1⟩.Exp
-- -- --   buildExp = ⊗-unit-r ∘g Automaton.Hom.fO (Automaton.fold alg) 0 where
-- -- --     open LL⟨1⟩ using (Exp; Atom)
-- -- --     open Automaton.Algebra
-- -- --     Stk : ℕ → Grammar ℓ-zero
-- -- --     Stk = Nat.elim ε
-- -- --       (λ _ Stk⟨n⟩ → literal RP ⊗ KL* (literal * ⊗ Atom) ⊗ Stk⟨n⟩)
-- -- --     alg : Automaton.Algebra ℓ-zero
-- -- --     alg .UO n = Exp ⊗ Stk n
-- -- --     alg .UC n = Stk n
-- -- --     alg .UM n = KL* (literal * ⊗ Atom) ⊗ Stk n
-- -- --     alg .[left] = ⊗-assoc ∘g ⊸3⊗ LL⟨1⟩.parens'
-- -- --     alg .[num] {n} = ⟜-intro⁻ (⊕-elim
-- -- --       -- the next thing was multiplying
-- -- --       (⟜-intro {k = Exp ⊗ Stk n} (⊗-assoc ∘g (LinΣ-elim λ _ → Atom.num) ,⊗ &-π₂))
-- -- --       -- the next thing was closing
-- -- --       (⟜-intro {k = Exp ⊗ Stk n} ((LinΣ-elim λ _ → Atom.num ,⊗ nil ∘g ⊗-unit-r⁻) ,⊗ &-π₂)))
-- -- --     alg .[rightClose] {n} = ⟜-intro⁻ (⊕-elim
-- -- --       -- next is multiplying
-- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ &-π₂))
-- -- --       -- next is more closing
-- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ (⊸0⊗ nil ∘g &-π₂))))
-- -- --     alg .[times] = ⊸2⊗ cons' ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻
-- -- --     alg .[done] = ⊸0⊗ nil

-- -- -- -- Completeness i.e., that every LL(1) parse has a trace. Though
-- -- -- -- completeness would be that every LL(1) parse corresponds to one we
-- -- -- -- extract from the previous function

-- -- -- -- kind of would want a truly dependent linear type here
-- -- -- -- to formulate it that way...
-- -- -- module Completeness where
-- -- --   open LL⟨1⟩.Hom
-- -- --   mkTrace : LL⟨1⟩.Exp ⊢ Automaton.Opening 0 true
-- -- --   mkTrace = (⊸-app ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,& Automaton.done) ∘g ⊗-unit-r⁻) ∘g LinΠ-app 0 ∘g LL⟨1⟩.fold the-alg .fE where
-- -- --     open LL⟨1⟩.Algebra
-- -- --     the-alg : LL⟨1⟩.Algebra ℓ-zero
-- -- --     -- need to update the motive: a UAs should also produce a proof that it starts with ε or *
-- -- --     the-alg .UE = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .UAs = LinΠ[ n ∈ ℕ ] (Automaton.DoneOpening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .UA = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .[mkExp] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       (((⊸-app ∘g LinΠ-app n ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻))
-- -- --     the-alg .[nil] = LinΠ-intro λ n → ⊸-intro-ε id
-- -- --     the-alg .[cons] = LinΠ-intro λ n → ⊸-intro {k = Automaton.DoneOpening n true}
-- -- --       (((((⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro) ,& Automaton.times) ∘g id ,⊗ ⊸-app) ∘g ⊗-assoc⁻) ∘g (id ,⊗ LinΠ-app n) ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)
-- -- --     the-alg .[num] {m} = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       (Automaton.num ∘g LinΣ-intro m ,⊗ id)
-- -- --     the-alg .[parens] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       ((Automaton.left ∘g id ,⊗ (⊸-app {g = Automaton.Opening (suc n) true} ∘g LinΠ-app (suc n) ,⊗ (⊕-inr ∘g (id ,⊗ ⊤-intro) ,& Automaton.rightClose)∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
