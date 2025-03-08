{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

data Tok : Type where
  [ ] : Tok     -- parens
  + : Tok       -- the binary operation
  num : ℕ → Tok -- constants

open Iso
opaque
  TokRep : Iso Tok (Bool ⊎ (Unit ⊎ ℕ))
  TokRep =
      iso
        (λ { [ → inl true ; ] → inl false ; + → inr (inl _) ; (num x) → inr (inr x)})
        (λ { (inl false) → ] ; (inl true) → [ ; (inr (inl x)) → + ; (inr (inr x)) → num x})
        (λ { (inl false) → refl ; (inl true) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl})
        λ { [ → refl ; ] → refl ; + → refl ; (num x) → refl}

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .leftInv)
      (isSet⊎ isSetBool (isSet⊎ isSetUnit isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

open import Grammar Alphabet hiding (_+)
open import Grammar.String.Properties Alphabet
open import Term Alphabet

open StrongEquivalence

anyNum : Grammar _
anyNum = ⊕[ n ∈ ℕ ] ＂ num n ＂

{--
-- Context-free grammar of expressions with binary operation *
-- over natural numbers and parentheses
--
-- S → E
-- E → A | A + E
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
        add → Var Atom ⊗e k ＂ + ＂ ⊗e Var Exp
  BinOpTy Atom =
    ⊕e (Tag Atom)
      λ where
        num → k anyNum
        parens → k ＂ [ ＂ ⊗e Var Exp ⊗e k ＂ ] ＂

  BinOpG : Nonterminal → Grammar ℓ-zero
  BinOpG = μ BinOpTy

  EXP = BinOpG Exp
  ATOM = BinOpG Atom

  -- DONE : ATOM ⊢ EXP
  -- DONE = roll ∘g ⊕ᴰ-in done ∘g liftG

  -- ADD : ATOM ⊗ ＂ + ＂ ⊗ EXP ⊢ EXP
  -- ADD = roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG ,⊗ liftG

  -- NUM : anyNum ⊢ ATOM
  -- NUM = roll ∘g ⊕ᴰ-in num ∘g liftG

  -- PARENS : ＂ [ ＂ ⊗ EXP ⊗ ＂ ] ＂ ⊢ ATOM
  -- PARENS = roll ∘g ⊕ᴰ-in parens ∘g liftG ,⊗ liftG ,⊗ liftG

module Automaton where
  data AutomatonState : Type ℓ-zero where
    Opening Closing Adding : AutomatonState

  data UnexpectedOpening : Type where
    EOF ] + : UnexpectedOpening

  uo : UnexpectedOpening → Grammar _
  uo EOF = ε
  uo ] = ＂ ] ＂ ⊗ ⊤
  uo + = ＂ + ＂ ⊗ ⊤

  data UnexpectedClosing : Type where
    EOF [ + aNum : UnexpectedClosing

  uc : UnexpectedClosing → Grammar _
  uc EOF = ε
  uc [ = ＂ [ ＂ ⊗ ⊤
  uc + = ＂ + ＂ ⊗ ⊤
  uc aNum = anyNum ⊗ ⊤

  data UnexpectedAdding : Type where
    [ ] aNum : UnexpectedAdding

  ua : UnexpectedAdding → Grammar _
  ua [ = ＂ [ ＂ ⊗ ⊤
  ua ] = ＂ ] ＂ ⊗ ⊤
  ua aNum = anyNum ⊗ ⊤

  data Guard : Type where
    ] ¬] : Guard

  data NotRP : Type where
    [ : NotRP       -- parens
    + : NotRP       -- the binary operation
    num : ℕ → NotRP -- constants

  notRP : NotRP → Tok
  notRP [ = [
  notRP + = +
  notRP (num x) = num x
  
  guard : Guard → Grammar _
  guard ] = ＂ ] ＂ ⊗ ⊤
  guard ¬] = ε ⊕ (⊕ᴰ {X = NotRP} λ t → ＂ notRP t ＂ ⊗ ⊤)

  Tok→Guard : Maybe Tok → Guard
  Tok→Guard nothing = ¬]
  Tok→Guard (just [) = ¬]
  Tok→Guard (just ]) = ]
  Tok→Guard (just +) = ¬]
  Tok→Guard (just (num x)) = ¬]

  Guard→State : Guard → AutomatonState
  Guard→State ] = Closing
  Guard→State ¬] = Adding

  -- the constructor names of each automaton state
  data AutomatonTag (b : Bool) (n : ℕ) : (N : AutomatonState) → Type ℓ-zero where
    left : AutomatonTag b n Opening
    num : AutomatonTag b n Opening
    unexpectedO : b Eq.≡ false → UnexpectedOpening → AutomatonTag b n Opening

    closeGood : ∀ n-1 → n Eq.≡ suc n-1 → AutomatonTag b n Closing
    closeBad : n Eq.≡ 0 → AutomatonTag b n Closing
    unexpectedC : b Eq.≡ false → UnexpectedClosing → AutomatonTag b n Closing

    doneGood : n Eq.≡ 0 → b Eq.≡ true → AutomatonTag b n Adding
    doneBad : ∀ n-1 → n Eq.≡ suc n-1 → b Eq.≡ false → AutomatonTag b n Adding
    add : AutomatonTag b n Adding
    unexpectedA : b Eq.≡ false → UnexpectedAdding → AutomatonTag b n Adding

  DoneOpeningFun : Bool → ℕ → Guard → Functor (ℕ × AutomatonState)
  DoneOpeningFun b n ] =
    &e Bool λ where
      true → k (guard ])
      false → Var (n , Closing)
  DoneOpeningFun b n ¬] =
    &e Bool λ where
      true → k (guard ¬])
      false → Var (n , Adding)

  DoneOpening : Bool → ℕ → Functor (ℕ × AutomatonState)
  DoneOpening b n = ⊕e Guard (DoneOpeningFun b n)

  AutomatonTy : Bool → ℕ → AutomatonState → Functor (ℕ × AutomatonState)
  AutomatonTy b n Opening =
    ⊕e (AutomatonTag b n Opening)
      λ where
        left → k ＂ [ ＂ ⊗e Var (suc n , Opening)
        num → k anyNum ⊗e DoneOpening b n
        (unexpectedO Eq.refl c) → k (uo c)
  AutomatonTy b n Closing =
    ⊕e (AutomatonTag b n Closing)
      λ where
        (closeGood n-1 Eq.refl) → k ＂ ] ＂ ⊗e DoneOpening b n-1
        (closeBad Eq.refl) → k (＂ ] ＂ ⊗ ⊤)
        (unexpectedC Eq.refl c) → k (uc c)
  AutomatonTy b n Adding =
    ⊕e (AutomatonTag b n Adding)
      λ where
        (doneGood Eq.refl Eq.refl) → k ε
        (doneBad n-1 Eq.refl Eq.refl) → k ε
        add → k ＂ + ＂ ⊗e Var (n , Opening)
        (unexpectedA Eq.refl c) → k (ua c)

  AutomatonTy' : Bool → ℕ × AutomatonState → Functor (ℕ × AutomatonState)
  AutomatonTy' b (n , s) = AutomatonTy b n s

  AutomatonG : Bool → ℕ × AutomatonState → Grammar ℓ-zero
  AutomatonG b = μ (AutomatonTy' b)

  peek : Maybe Tok → Grammar ℓ-zero
  peek = Maybe.rec ε (λ c → ＂ c ＂ ⊗ ⊤)


  -- After peeking, we choose a subsequent Guard and
  -- AutomatonState to transition to
  -- Here we ensure that the chosen guard and state match
  -- the ones prescribed by DoneOpening
  -- mkGuardPfs' : ∀ (b : Bool) → (n : ℕ) →
  --   (tok? : Maybe Tok) →
  --   peek tok? & AutomatonG  b (n , (Guard→State (Tok→Guard tok?))) ⊢
  --     ⟦ DoneOpeningFun b n (Tok→Guard tok?) ⟧
  --       (λ (n , s) → AutomatonG b (n , s))
  -- mkGuardPfs' b n nothing = &ᴰ-in λ where
  --     false → liftG ∘g &-π₂
  --     true → liftG ∘g ⊕-inl ∘g &-π₁
  -- mkGuardPfs' b n (just [) = &ᴰ-in λ where
  --     false → liftG ∘g &-π₂
  --     true → liftG ∘g ⊕-inr ∘g ⊕ᴰ-in [ ∘g &-π₁
  -- mkGuardPfs' b n (just ]) = &ᴰ-in λ where
  --     false → liftG ∘g &-π₂
  --     true → liftG ∘g &-π₁
  -- mkGuardPfs' b n (just +) = &ᴰ-in λ where
  --     false → liftG ∘g &-π₂
  --     true → liftG ∘g ⊕-inr ∘g ⊕ᴰ-in NotRP.+ ∘g &-π₁
  -- mkGuardPfs' b n (just (num m)) = &ᴰ-in λ where
  --     false → liftG ∘g &-π₂
  --     true → liftG ∘g ⊕-inr ∘g ⊕ᴰ-in (num m) ∘g &-π₁

  -- Whenever we want to use a Guard, this cuts out
  -- the redundant work in checking the guardedness condition
  mkGuardPfs : (tok : Tok) → (n : ℕ) →
    ＂ tok ＂ ⊗
      (&[ nq ∈ ℕ × AutomatonState ]
      ⊕[ b ∈ Bool ]
      AutomatonG b nq)
    ⊢
    ⊕[ b ∈ Bool ]
      (＂ tok ＂ ⊗
        (⊕[ g ∈ Guard ] ⟦ DoneOpeningFun b n g ⟧ (AutomatonG b)))
  mkGuardPfs tok n =
    ⊕-elim
      {!!}
      {!!}
    ∘g ⊗⊕-distL
    ∘g id ,⊗ firstChar≅ .fun
    -- ⊕ᴰ-elim (λ tok? →
    --   map⊕ᴰ (λ b →
    --     id ,⊗ (⊕ᴰ-in (Tok→Guard tok?) ∘g mkGuardPfs' b n tok?)
    --   )
    --   ∘g ⊕ᴰ-distR .fun
    --   ∘g id ,⊗ (&⊕ᴰ-distR≅ .fun ∘g (id ,&p &ᴰ-π (Guard→State (Tok→Guard tok?))))
    -- )
    -- ∘g ⊕ᴰ-distR .fun
    -- ∘g id ,⊗ &⊕ᴰ-distL≅ .fun
    -- ∘g id ,⊗ &ᴰ-π n

  directParse : string ⊢
    &[ nq ∈ ℕ × AutomatonState ]
    ⊕[ b ∈ Bool ]
    AutomatonG b nq
  directParse = fold*r' _
    ((&ᴰ-in λ where
      (n , Opening) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl EOF)
      (n , Closing) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl EOF)
      (zero , Adding) → ⊕ᴰ-in true ∘g roll ∘g ⊕ᴰ-in (doneGood Eq.refl Eq.refl)
      (suc n-1 , Adding) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (doneBad n-1 Eq.refl Eq.refl))
      ∘g liftG)
    ((&ᴰ-in λ where
      (n , Opening) → ⊕ᴰ-elim λ where
        [ → map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in left ∘g liftG ,⊗ liftG)
            ∘g ⊕ᴰ-distR .fun
           ∘g id ,⊗ &ᴰ-π (suc n , Opening)
        ] → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl ]) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl +) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) →
          map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id ∘g ⊕ᴰ-in x ,⊗ id)
          ∘g mkGuardPfs (num x) n
      (zero , Closing) →
        ⊕ᴰ-elim λ where
        [ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (closeBad Eq.refl) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl UnexpectedClosing.+) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl aNum) ∘g liftG ∘g ⊕ᴰ-in x  ,⊗ ⊤-intro
      (suc n-1 , Closing) →
        ⊕ᴰ-elim λ where
        [ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in (closeGood n-1 Eq.refl) ∘g liftG ,⊗ id)
            ∘g mkGuardPfs ] n-1
        + → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl UnexpectedClosing.+) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl aNum) ∘g liftG ∘g ⊕ᴰ-in x  ,⊗ ⊤-intro
      (n , Adding) → ⊕ᴰ-elim λ where
        [ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl ]) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG)
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ &ᴰ-π (n , Opening)
        (num x) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl aNum) ∘g liftG ∘g (⊕ᴰ-in x) ,⊗ ⊤-intro )
      ∘g ⊕ᴰ-distL .fun
      )

  parseTy =
    &[ n ∈ ℕ ]
    &[ s ∈ AutomatonState ]
    ⊕[ b ∈ Bool ]
      AutomatonG b (n , s)

  goal = ⊕ᴰ peek & parseTy


  parse' : string ⊢ goal
  parse' = {!!}
    -- fold*r char λ where
    --   (lift _) →
    --     ⊕ᴰ-elim λ where
    --       nil →
    --         (⊕ᴰ-in nothing ∘g lowerG ∘g lowerG) ,&
    --         &ᴰ-in λ n → &ᴰ-in λ where
    --           Opening →
    --             ⊕ᴰ-in false ∘g roll
    --             ∘g ⊕ᴰ-in (unexpectedO Eq.refl EOF) ∘g lowerG
    --           Closing →
    --             ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl EOF) ∘g lowerG
    --           Adding →
    --             Nat.elim {A = λ n → LiftG ℓ-zero ε* ⊢ ⊕[ b ∈ Bool ] AutomatonG b (n , Adding)}
    --               (⊕ᴰ-in true ∘g roll
    --                 ∘g ⊕ᴰ-in (doneGood Eq.refl Eq.refl) ∘g lowerG)
    --               (λ n-1 _ →
    --                 ⊕ᴰ-in false ∘g roll
    --                 ∘g ⊕ᴰ-in (doneBad n-1 Eq.refl Eq.refl) ∘g lowerG)
    --               n
    --       cons →
    --         ⊕ᴰ-elim (λ tok → ⊕ᴰ-in (just tok) ∘g id ,⊗ ⊤-intro) ,&
    --         (&ᴰ-in λ n → &ᴰ-in λ where
    --           Opening → ⊕ᴰ-elim λ where
    --             [ →
    --               map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in left ∘g liftG ,⊗ liftG)
    --               ∘g ⊕ᴰ-distR .fun
    --               ∘g id ,⊗ (&ᴰ-π Opening ∘g &ᴰ-π (suc n) ∘g &-π₂)
    --             ] → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl ])
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             + → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl UnexpectedOpening.+)
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             (num m) →
    --               map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id ∘g ⊕ᴰ-in m ,⊗ id)
    --               ∘g mkGuardPfs (num m) n
    --           Closing → ⊕ᴰ-elim λ where
    --             [ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl [)
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             ] →
    --               Nat.elim {A = λ n → ＂ ] ＂ ⊗ goal ⊢ ⊕[ b ∈ Bool ] AutomatonG b (n , Closing)}
    --                 (⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (closeBad Eq.refl) ∘g liftG ∘g id ,⊗ ⊤-intro)
    --                 (λ n-1 _ →
    --                   map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in (closeGood n-1 Eq.refl) ∘g liftG ,⊗ id)
    --                   ∘g mkGuardPfs ] n-1
    --                 )
    --                 n
    --             + → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl UnexpectedClosing.+)
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             (num m) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl aNum)
    --                       ∘g liftG ∘g ⊕ᴰ-in m  ,⊗ ⊤-intro
    --           Adding → ⊕ᴰ-elim λ where
    --             [ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl [)
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             ] → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl ])
    --                 ∘g liftG ∘g id ,⊗ ⊤-intro
    --             + →
    --               map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG)
    --               ∘g ⊕ᴰ-distR .fun
    --               ∘g id ,⊗ (&ᴰ-π Opening ∘g &ᴰ-π n ∘g &-π₂)
    --             (num m) → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl aNum)
    --                       ∘g liftG ∘g ⊕ᴰ-in m  ,⊗ ⊤-intro
    --         )
    --         ∘g ⊕ᴰ-distL .fun
    --         ∘g lowerG ,⊗ lowerG

  printAlg : (b : Bool) →
    Algebra (AutomatonTy' b) (λ _ → string)
  printAlg b (n , Opening) =
    ⊕ᴰ-elim λ where
      left →
        CONS
        ∘g literal→char [ ,⊗ id
        ∘g lowerG ,⊗ lowerG
      num →
        ⊕ᴰ-elim (λ m →
          ⊕ᴰ-elim (λ where
            ] → CONS ∘g literal→char (num m) ,⊗ (lowerG ∘g &ᴰ-π false)
            ¬] → CONS ∘g literal→char (num m) ,⊗ (lowerG ∘g &ᴰ-π false)
          )
          ∘g ⊕ᴰ-distR .fun
        )
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG ,⊗ id
      (unexpectedO Eq.refl EOF) →
        NIL ∘g lowerG
      (unexpectedO Eq.refl ]) →
        CONS
        ∘g literal→char ] ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedO Eq.refl +) →
        CONS
        ∘g literal→char Tok.+ ,⊗ ⊤→string
        ∘g lowerG
  printAlg b (n , Closing) =
    ⊕ᴰ-elim λ where
      (closeGood n-1 Eq.refl) →
        ⊕ᴰ-elim (λ where
          ] → CONS ∘g literal→char ] ,⊗ (lowerG ∘g &ᴰ-π false)
          ¬] → CONS ∘g literal→char ] ,⊗ (lowerG ∘g &ᴰ-π false)
        )
        ∘g ⊕ᴰ-distR .fun
        ∘g lowerG ,⊗ id
      (closeBad Eq.refl) →
        CONS
        ∘g literal→char ] ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedC Eq.refl EOF) → NIL ∘g lowerG
      (unexpectedC Eq.refl [) →
        CONS
        ∘g literal→char [ ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedC Eq.refl +) →
        CONS
        ∘g literal→char Tok.+ ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedC Eq.refl aNum) →
        ⊕ᴰ-elim (λ m → CONS ∘g literal→char (num m) ,⊗ ⊤→string)
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG
  printAlg b (n , Adding) =
    ⊕ᴰ-elim λ where
      (doneGood Eq.refl Eq.refl) → NIL ∘g lowerG
      (doneBad n-1 Eq.refl Eq.refl) → NIL ∘g lowerG
      add →
        CONS
        ∘g literal→char Tok.+ ,⊗ id
        ∘g lowerG ,⊗ lowerG
      (unexpectedA Eq.refl [) →
        CONS
        ∘g literal→char [ ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedA Eq.refl ]) →
        CONS
        ∘g literal→char ] ,⊗ ⊤→string
        ∘g lowerG
      (unexpectedA Eq.refl aNum) →
        ⊕ᴰ-elim (λ m → CONS ∘g literal→char (num m) ,⊗ ⊤→string)
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG

  print : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
    AutomatonG b (n , s) ⊢ string
  print b n s = rec (AutomatonTy' b) (printAlg b) (n , s)

  parse :
    (n : ℕ) →
    (s : AutomatonState) →
    string ⊢ ⊕[ b ∈ Bool ] AutomatonG b (n , s)
  parse n s = &ᴰ-π s ∘g &ᴰ-π n ∘g &-π₂ ∘g parse'

  ⊕ᴰAlg : (b : Bool) →
    Algebra
      (AutomatonTy' b)
      (λ (n , s) → ⊕[ b' ∈ Bool ] AutomatonG b' (n , s))
  ⊕ᴰAlg b (n , Opening) =
    ⊕ᴰ-elim λ where
      left →
        map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in left ∘g liftG ,⊗ liftG)
        ∘g ⊕ᴰ-distR .fun
        ∘g lowerG ,⊗ lowerG
      num →
        {!!}
        -- ⊕ᴰ-elim (λ where
        --   ] →
        --     {!!}
        --     ∘g roll {F = AutomatonTy' b} {x = (n , Opening)}
        --     ∘g ⊕ᴰ-in num
        --     ∘g liftG ,⊗ ((⊕ᴰ-in ] ∘g {!!} ∘g lowerG) ∘g &ᴰ-π false)
        --   ¬] → {!!}
        -- )
        -- ∘g ⊕ᴰ-distR .fun
        -- ∘g lowerG ,⊗ id
      (unexpectedO Eq.refl c) → {!!}
  ⊕ᴰAlg b (n , Closing) =
    ⊕ᴰ-elim λ where
      (closeGood n-1 Eq.refl) → {!!}
      (closeBad Eq.refl) → {!!}
      (unexpectedC Eq.refl c) → {!!}
  ⊕ᴰAlg b (n , Adding) =
    ⊕ᴰ-elim λ where
      (doneGood Eq.refl Eq.refl) → {!!}
      (doneBad n-1 Eq.refl Eq.refl) → {!!}
      add → {!!}
      (unexpectedA Eq.refl c) → {!!}

  Trace≅string :
    (n : ℕ) → (s : AutomatonState) →
    (⊕[ b ∈ Bool ] AutomatonG b (n , s)) ≅ string
  Trace≅string n s .fun = ⊕ᴰ-elim (λ b → print b n s)
  Trace≅string n s .inv = parse n s
  Trace≅string n s .sec = unambiguous-string _ _
  Trace≅string n s .ret = isRetract
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      isRetract : parse n s ∘g ⊕ᴰ-elim (λ b → print b n s) ≡ id
      isRetract = ⊕ᴰ≡ _ _ λ b →
        ind'
          (AutomatonTy' b)
          (⊕ᴰAlg b)
          ((λ (n , q) → parse n q ∘g print b n q) , {!!})
          ((λ (n , q) → ⊕ᴰ-in b) , λ (n , q) → {!!})
          (n , s)

-- {- Grammar for one associative binary operation with constants and parens -}
-- {-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- module Examples.BinOp where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels

-- open import Cubical.Data.Bool hiding (_⊕_)
-- open import Cubical.Data.Maybe as Maybe
-- open import Cubical.Data.Nat as Nat
-- open import Cubical.Data.FinSet
-- open import Cubical.Data.Sum as Sum
-- open import Cubical.Data.Sigma

-- -- TODO need to make this work with opaqueness
-- -- data Tok : Type where
-- --   LP RP : Tok   -- parens
-- --   * : Tok       -- the binary operation
-- --   num : ℕ → Tok -- constants

-- -- Alphabet : hSet _
-- -- Alphabet = Tok , isSetRetract encode decode dex≡x (isSet⊎ isSetFin isSetℕ)
-- --   where
-- --   open import Cubical.Data.Sum as Sum
-- --   open import Cubical.Data.Fin as Fin
-- --   Tok' = Fin 3 ⊎ ℕ
-- --   encode : Tok → Tok'
-- --   encode LP = inl 0
-- --   encode RP = inl 1
-- --   encode * = inl 2
-- --   encode (num x) = inr x
-- --   decode : Tok' → Tok
-- --   decode (inl (0 , snd₁)) = LP
-- --   decode (inl (1 , snd₁)) = RP
-- --   decode (inl (suc (suc fst₁) , snd₁)) = *
-- --   decode (inr x) = num x
-- --   dex≡x : ∀ x → decode (encode x) ≡ x
-- --   dex≡x LP = refl
-- --   dex≡x RP = refl
-- --   dex≡x * = refl
-- --   dex≡x (num x) = refl

-- -- open import Grammar Alphabet
-- -- open import Grammar.Equivalence Alphabet
-- -- open import Term Alphabet

-- -- anyNum : Grammar _
-- -- anyNum = LinΣ[ n ∈ ℕ ] literal (num n)
-- -- module LL⟨1⟩ where
-- --   Exp : Grammar ℓ-zero
-- --   data Atom : Grammar ℓ-zero

-- --   Exp = Atom ⊗' (KL* (literal * ⊗' Atom))
-- --   data Atom where
-- --     num : ∀ {n} → literal (num n) ⊢ Atom
-- --     parens :
-- --       literal LP ⊗' Exp ⊗' literal RP ⊢ Atom

-- --   -- This grammar is LL(1) because after you match a close paren, you
-- --   -- need to look ahead one token to know if you continue matching
-- --   -- close parens or have finished parsing the Atom.
-- --   opaque
-- --     unfolding _⊗_
-- --     num' : ∀ {n} → ε ⊢ Atom ⊸ literal (num n)
-- --     num' {n} = ⊸-intro-ε {k = Atom} (num {n})
-- --     parens' : ε ⊢ Atom ⊸ literal RP ⊸ Exp ⊸ literal LP
-- --     parens' = ⊸3-intro-ε parens

-- --   record Algebra ℓ : Type (ℓ-suc ℓ) where
-- --     field
-- --       UE : Grammar ℓ
-- --       UAs : Grammar ℓ
-- --       UA : Grammar ℓ

-- --       [mkExp] : UA ⊗ UAs ⊢ UE
-- --       [nil] : ε ⊢ UAs
-- --       [cons] : (literal * ⊗ UA) ⊗ UAs ⊢ UAs
-- --       [num] : ∀ {n} → literal (num n) ⊢ UA
-- --       [parens] : literal LP ⊗ UE ⊗ literal RP ⊢ UA

-- --   open Algebra
-- --   opaque
-- --     unfolding _⊗_
-- --     initialAlgebra : Algebra ℓ-zero
-- --     initialAlgebra .UE = Exp
-- --     initialAlgebra .UAs = KL* (literal * ⊗ Atom)
-- --     initialAlgebra .UA = Atom
-- --     initialAlgebra .[mkExp] = id
-- --     initialAlgebra .[nil] = nil
-- --     initialAlgebra .[cons] = cons
-- --     initialAlgebra .[num] = num
-- --     initialAlgebra .[parens] = parens
-- --   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
-- --     field
-- --       fE : A .UE ⊢ B .UE
-- --       fAs : A .UAs ⊢ B .UAs
-- --       fA : A .UA ⊢ B .UA

-- --   -- this can be avoided by doing manual recursion for rAs
-- --   opaque
-- --     unfolding _⊗_ initialAlgebra
-- --     fold : ∀ {ℓ}(A : Algebra ℓ) → Hom initialAlgebra A
-- --     fold A = record { fE = rE ; fAs = rAs ; fA = rA } where
-- --       rE : Exp ⊢ A .UE
-- --       rAs : KL* (literal * ⊗ Atom) ⊢ A .UAs
-- --       rA : Atom ⊢ A .UA
-- --       rE _ (sp , a , as) = A .[mkExp] _ (sp , rA _ a , rAs _ as)
-- --       rAs _ (KL*.nil _ x) = A .[nil] _ x
-- --       rAs _ (KL*.cons _ (sp1 , (sp2 , star , a) , as)) = A .[cons] _ (sp1 , (sp2 , star , rA _ a) , rAs _ as)
-- --       rA _ (num _ x) = A .[num] _ x
-- --       rA _ (parens _ (sp1 , lp , sp2 , e , rp)) = A .[parens] _ (sp1 , lp , sp2 , rE _ e , rp)

-- -- module Automaton where
-- --   -- TODO: we should be able to generalize this definition to an
-- --   -- (infinite state) deterministic automaton with guarded
-- --   -- transitions.

-- --   -- the stack is a number,
-- --   -- the number of open parens that are closed by the term

-- --   -- Exp is for when we are parsing a single expression, Suffix is
-- --   -- when we are parsing the sequence of multiplications after an
-- --   -- expression

-- --   -- the boolean is whether it is an accepting or rejecting trace

-- --   -- three cases: Opening, Closing, Multiplying

-- --   -- Opening: at the start of an expression, the term starts with a
-- --   -- sequence of 0 or more opening parens, which we count. Ends when
-- --   -- we see a number, then we use lookahead to determine whether to
-- --   -- parse closing parens or start parsing a multiplication sequence
-- --   data Opening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- --   -- Closing: parse as many closing parens as you can, eventually
-- --   -- use lookahead to decide when to start parsing multiplication sequence
-- --   data Closing : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- --   -- Parse a sequence of * Exps
-- --   data Multiplying : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- --   DoneOpening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- --   DoneOpening n b =
-- --     ((ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤) &' Multiplying n b)
-- --     ⊕' ((literal RP ⊗' ⊤) &' Closing n b)
-- --   data Opening where
-- --     left : ∀ {n b} → literal LP ⊗' Opening (suc n) b ⊢ Opening n b
-- --     num  : ∀ {n b} →
-- --       (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗' DoneOpening n b ⊢ Opening n b
-- --     unexpected : ∀ {n} → ε ⊕' (literal RP ⊕' literal *) ⊗' ⊤ ⊢ Opening n false

-- --   data Closing where
-- --     rightClose : ∀ {n b} →
-- --       literal RP ⊗' DoneOpening n b ⊢ Closing (suc n) b
-- --     rightUnmatched : literal RP ⊗' ⊤ ⊢ Closing 0 false
-- --     unexpected : ∀ {n} → ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤ ⊢ Closing n false

-- --   data Multiplying where
-- --     done : ε ⊢ Multiplying 0 true
-- --     times : ∀ {n b} → literal * ⊗' Opening n b ⊢ Multiplying n b
-- --     unmatched : ∀ {n} → ε ⊢ Multiplying (suc n) false
-- --     unexpected : ∀ {n} →
-- --       (literal LP ⊕' literal RP ⊕' anyNum) ⊗' ⊤ ⊢ Multiplying n false

-- --   -- note this is for the true cases, the tautological one would also
-- --   -- have false cases but we would just use ⊥ for them.
-- --   --
-- --   -- because of this we are getting a `warning: -W[no]UnsupportedIndexedMatch`
-- --   record Algebra ℓ : Type (ℓ-suc ℓ) where
-- --     field
-- --       UO : ℕ → Grammar ℓ
-- --       UC : ℕ → Grammar ℓ
-- --       UM : ℕ → Grammar ℓ
-- --     UDO : ℕ → Grammar ℓ
-- --     UDO n = ((ε ⊕ (literal * ⊕ literal LP ⊕ anyNum) ⊗ ⊤) & UM n)
-- --       ⊕ ((literal RP ⊗ ⊤) & UC n)
-- --     field
-- --       [left] : ∀ {n} → literal LP ⊗ UO (suc n) ⊢ UO n
-- --       [num]  : ∀ {n} → (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ UDO n ⊢ UO n
-- --       [rightClose] : ∀ {n} → literal RP ⊗ UDO n ⊢ UC (suc n)
-- --       [done] : ε ⊢ UM 0
-- --       [times] : ∀ {n} → literal * ⊗ UO n ⊢ UM n

-- --   open Algebra
-- --   opaque
-- --     unfolding _⊗_ _⊕_ _&_
-- --     initialAlgebra : Algebra ℓ-zero
-- --     initialAlgebra .UO n = Opening n true
-- --     initialAlgebra .UC n = Closing n true
-- --     initialAlgebra .UM n = Multiplying n true
-- --     initialAlgebra .[left] = left
-- --     initialAlgebra .[num] = num
-- --     initialAlgebra .[rightClose] = rightClose
-- --     initialAlgebra .[times] = times
-- --     initialAlgebra .[done] = done

-- --   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
-- --     field
-- --       fO : ∀ n → A .UO n ⊢ B .UO n
-- --       fC : ∀ n → A .UC n ⊢ B .UC n
-- --       fM : ∀ n → A .UM n ⊢ B .UM n
-- --       -- TODO: the equations

-- --   opaque
-- --     unfolding _⊗_ _⊕_ _&_ initialAlgebra
-- --     -- TODO these defs need indexed pattern matching
-- --     fold : ∀ {ℓ} (A : Algebra ℓ) → Hom initialAlgebra A
-- --     fold A = record { fO = rO ; fC = rC ; fM = rM } where
-- --       rO : ∀ n → Opening n true ⊢ A .UO n
-- --       rC : ∀ n → Closing n true ⊢ A .UC n
-- --       rM : ∀ n → Multiplying n true ⊢ A .UM n
-- --       rDO : ∀ n → DoneOpening n true ⊢ UDO A n
-- --       rO n w (left _ (sp , lp , o)) = A .[left] w (sp , (lp , rO _ _ o))
-- --       rO n w (num _ (sp , m , doo)) = A .[num] _ (sp , m , rDO _ _ doo)
-- --       rC _ w (rightClose _ (sp , rp , doo)) = A .[rightClose] _ (sp , rp , rDO _ _ doo)
-- --       rM _ w (done _ x) = A .[done] _ x
-- --       rM _ w (times _ (sp , star , o)) = A .[times] _ (sp , star , rO _ _ o)
-- --       rDO n w (inl x) = inl ((x .fst) , (rM _ _ (x .snd)))
-- --       rDO n w (inr x) = inr (x .fst , rC _ _ (x .snd))
-- --     Peek : Maybe Tok → Grammar ℓ-zero
-- --     Peek = Maybe.rec ε (λ c → literal c ⊗ ⊤)

-- --     Goal : Grammar ℓ-zero
-- --     Goal = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- --       (LinearΣ (Opening n)
-- --       & LinearΣ (Closing n)
-- --       & LinearΣ (Multiplying n))

-- --     -- TODO typechecking this parse term is very slow
-- --     -- Should probably split it into several pieces
-- -- --     opaque
-- -- --       -- unfolding LL⟨1⟩.fold LL⟨1⟩.num' LL⟨1⟩.parens' LL⟨1⟩.initialAlgebra _⊗_ _⊕_ _&_ _⇒_ ⊕-elim ⇒-intro ⇐-intro ⟜-intro ⟜-app ⊸-intro ⊸-app KL*r-elim fold initialAlgebra ⊗-intro &-intro &-π₁ &-π₂ ⊕-inl ⊕-inr ⇒-app
-- -- --       parse' : string ⊢ LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- -- --         (LinearΣ (Opening n)
-- -- --         & LinearΣ (Closing n)
-- -- --         & LinearΣ (Multiplying n))
-- -- --       parse' = foldKL*r char
-- -- --         (record {
-- -- --           the-ℓ = ℓ-zero
-- -- --         ; G = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- -- --               (LinearΣ (Opening n)
-- -- --               & LinearΣ (Closing n)
-- -- --               & LinearΣ (Multiplying n))
-- -- --         ; nil-case =
-- -- --           LinΣ-intro Maybe.nothing
-- -- --           ,& LinΠ-intro λ n →
-- -- --             (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- --             ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- --             ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))}
--                      (LinΣ-intro true ∘g done)
--                      (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- -- --         ; cons-case =
-- -- --           (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- -- --             (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- -- --           ,& LinΠ-intro λ n →
-- -- --             {!!}
-- -- --         })
-- -- --       -- foldKL*r _ (record { the-ℓ = _ ; G = _
-- -- --       --   ; nil-case =
-- -- --       --     LinΣ-intro Maybe.nothing
-- -- --       --     ,& LinΠ-intro λ n →
-- -- --       --     (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- --       --     ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- --       --     ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- -- --       --   ; cons-case =
-- -- --       --     (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- -- --       --       (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- -- --       --     ,& LinΠ-intro λ n →
-- -- --       --       (⊸-intro⁻
-- -- --       --         (LinΣ-elim λ
-- -- --       --         { (num x) → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- --       --           -- goto closing
-- -- --       --           { (just RP) → ⇒-intro (⇐-intro⁻ (((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ ⊕-inr))) ∘g &-π₁) ∘g &-π₂))
-- -- --       --           ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --           ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --           ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --           ; (just (num y)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro y) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --           }))
-- -- --       --           ∘g id ,⊗ id ,&p LinΠ-app n)
-- -- --       --           --  (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- --       --         ; LP → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (((LinΣ-elim (λ b → ⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g left)) ∘g &-π₁)) ∘g LinΠ-app (suc n) ∘g &-π₂))
-- -- --       --         ; RP → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- --       --         ; * → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inr ,⊗ ⊤-intro)
-- -- --       --         })
-- -- --       --       )
-- -- --       --       -- ⊸-intro⁻
-- -- --       --       ,& ⊸-intro⁻ (LinΣ-elim λ
-- -- --       --        { RP → ⊸-intro {k = LinearΣ (Closing n)} (Nat.elim {A = λ n → Term (literal RP ⊗ Goal) (LinearΣ (Closing n))}
-- -- --       --          -- empty stack
-- -- --       --          (LinΣ-intro false ∘g rightUnmatched ∘g id ,⊗ ⊤-intro)
-- -- --       --          -- popped
-- -- --       --          (λ n-1 _ → (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- --       --            { (just RP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ ⊕-inr))) ∘g &-π₁ ∘g &-π₂))
-- -- --       --            ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --            ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --            ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --            ; (just (num x)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- --       --            })) ∘g id ,⊗ id ,&p LinΠ-app n-1))
-- -- --       --          n)
-- -- --       --        ; LP → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- -- --       --        ; * → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- --       --          unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro)
-- -- --       --        })
-- -- --       --       ,&
-- -- --       --      (⊸-intro⁻ (LinΣ-elim λ
-- -- --       --        { * → ⊸-intro {k = LinearΣ (Multiplying n)} (⟜-intro⁻ ((((LinΣ-elim λ b → ⟜-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro b ∘g times)) ∘g &-π₁) ∘g LinΠ-app n) ∘g &-π₂))
-- -- --       --        ; LP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- --       --        ; RP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- -- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro) }))
-- -- --       --   })

-- -- -- --     parse : string ⊢ LinΣ[ b ∈ Bool ] Opening zero b
-- -- -- --     parse = ((&-π₁ ∘g LinΠ-app zero) ∘g &-π₂) ∘g parse'

-- -- -- -- -- Soundness: i.e., that from every trace we can extract an LL(1) parse
-- -- -- -- module Soundness where
-- -- -- --   buildExp : Automaton.Opening 0 true ⊢ LL⟨1⟩.Exp
-- -- -- --   buildExp = ⊗-unit-r ∘g Automaton.Hom.fO (Automaton.fold alg) 0 where
-- -- -- --     open LL⟨1⟩ using (Exp; Atom)
-- -- -- --     open Automaton.Algebra
-- -- -- --     Stk : ℕ → Grammar ℓ-zero
-- -- -- --     Stk = Nat.elim ε
-- -- -- --       (λ _ Stk⟨n⟩ → literal RP ⊗ KL* (literal * ⊗ Atom) ⊗ Stk⟨n⟩)
-- -- -- --     alg : Automaton.Algebra ℓ-zero
-- -- -- --     alg .UO n = Exp ⊗ Stk n
-- -- -- --     alg .UC n = Stk n
-- -- -- --     alg .UM n = KL* (literal * ⊗ Atom) ⊗ Stk n
-- -- -- --     alg .[left] = ⊗-assoc ∘g ⊸3⊗ LL⟨1⟩.parens'
-- -- -- --     alg .[num] {n} = ⟜-intro⁻ (⊕-elim
-- -- -- --       -- the next thing was multiplying
-- -- -- --       (⟜-intro {k = Exp ⊗ Stk n} (⊗-assoc ∘g (LinΣ-elim λ _ → Atom.num) ,⊗ &-π₂))
-- -- -- --       -- the next thing was closing
-- -- -- --       (⟜-intro {k = Exp ⊗ Stk n} ((LinΣ-elim λ _ → Atom.num ,⊗ nil ∘g ⊗-unit-r⁻) ,⊗ &-π₂)))
-- -- -- --     alg .[rightClose] {n} = ⟜-intro⁻ (⊕-elim
-- -- -- --       -- next is multiplying
-- -- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ &-π₂))
-- -- -- --       -- next is more closing
-- -- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ (⊸0⊗ nil ∘g &-π₂))))
-- -- -- --     alg .[times] = ⊸2⊗ cons' ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻
-- -- -- --     alg .[done] = ⊸0⊗ nil

-- -- -- -- -- Completeness i.e., that every LL(1) parse has a trace. Though
-- -- -- -- -- completeness would be that every LL(1) parse corresponds to one we
-- -- -- -- -- extract from the previous function

-- -- -- -- -- kind of would want a truly dependent linear type here
-- -- -- -- -- to formulate it that way...
-- -- -- -- module Completeness where
-- -- -- --   open LL⟨1⟩.Hom
-- -- -- --   mkTrace : LL⟨1⟩.Exp ⊢ Automaton.Opening 0 true
-- -- -- --   mkTrace = (⊸-app ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,& Automaton.done) ∘g ⊗-unit-r⁻) ∘g LinΠ-app 0 ∘g LL⟨1⟩.fold the-alg .fE where
-- -- -- --     open LL⟨1⟩.Algebra
-- -- -- --     the-alg : LL⟨1⟩.Algebra ℓ-zero
-- -- -- --     -- need to update the motive: a UAs should also produce a proof that it starts with ε or *
-- -- -- --     the-alg .UE = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- -- --     the-alg .UAs = LinΠ[ n ∈ ℕ ] (Automaton.DoneOpening n true ⊸ Automaton.DoneOpening n true)
-- -- -- --     the-alg .UA = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- -- --     the-alg .[mkExp] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- --       (((⊸-app ∘g LinΠ-app n ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻))
-- -- -- --     the-alg .[nil] = LinΠ-intro λ n → ⊸-intro-ε id
-- -- -- --     the-alg .[cons] = LinΠ-intro λ n → ⊸-intro {k = Automaton.DoneOpening n true}
-- -- -- --       (((((⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro) ,& Automaton.times) ∘g id ,⊗ ⊸-app) ∘g ⊗-assoc⁻) ∘g (id ,⊗ LinΠ-app n) ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)
-- -- -- --     the-alg .[num] {m} = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- --       (Automaton.num ∘g LinΣ-intro m ,⊗ id)
-- -- -- --     the-alg .[parens] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- --       ((Automaton.left ∘g id ,⊗ (⊸-app {g = Automaton.Opening (suc n) true} ∘g LinΠ-app (suc n) ,⊗ (⊕-inr ∘g (id ,⊗ ⊤-intro) ,& Automaton.rightClose)∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
