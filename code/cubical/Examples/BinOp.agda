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
open import Cubical.Data.Sum as Sum using (_⊎_)
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
        (λ { [ → Sum.inl true ; ] → Sum.inl false ; + → Sum.inr (Sum.inl _) ; (num x) → Sum.inr (Sum.inr x)})
        (λ { (Sum.inl false) → ] ; (Sum.inl true) → [ ; (Sum.inr (Sum.inl x)) → + ; (Sum.inr (Sum.inr x)) → num x})
        (λ { (Sum.inl false) → refl ; (Sum.inl true) → refl ; (Sum.inr (Sum.inl x)) → refl ; (Sum.inr (Sum.inr x)) → refl})
        λ { [ → refl ; ] → refl ; + → refl ; (num x) → refl}

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .leftInv)
      (Sum.isSet⊎ isSetBool (Sum.isSet⊎ isSetUnit isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

open import Grammar Alphabet hiding (_+)
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

  DONE : ATOM ⊢ EXP
  DONE = roll ∘g σ done ∘g liftG

  ADD : ATOM ⊗ ＂ + ＂ ⊗ EXP ⊢ EXP
  ADD = roll ∘g σ add ∘g liftG ,⊗ liftG ,⊗ liftG

  NUM : anyNum ⊢ ATOM
  NUM = roll ∘g σ num ∘g liftG

  PARENS : ＂ [ ＂ ⊗ EXP ⊗ ＂ ] ＂ ⊢ ATOM
  PARENS = roll ∘g σ parens ∘g liftG ,⊗ liftG ,⊗ liftG

  ATOM*→EXP : ATOM ⊗ (＂ + ＂ ⊗ ATOM) * ⊢ EXP
  ATOM*→EXP = ⟜-intro⁻
      (fold*r _
        (⟜-intro (DONE ∘g ⊗-unit-r))
        (⟜-intro (ADD ∘g id ,⊗ (id ,⊗ ⟜-app ∘g ⊗-assoc⁻))))

  unrollEXPAlg :
    Algebra BinOpTy (λ where
      Exp → ATOM ⊕ (ATOM ⊗ (＂ + ＂ ⊗ ATOM) *)
      Atom → ATOM
    )
  unrollEXPAlg Exp =
    ⊕ᴰ-elim (λ where
      done → inl ∘g lowerG
      add →
        (inr
        ∘g id ,⊗ (CONS ∘g
          ⊕-elim
            (id ,⊗ NIL ∘g ⊗-unit-r⁻)
            ⊗-assoc
          ∘g ⊗⊕-distL
        ))
        ∘g lowerG ,⊗ lowerG ,⊗ lowerG
    )
  unrollEXPAlg Atom = ⊕ᴰ-elim λ where
    num → NUM ∘g lowerG
    parens →
      ⊕-elim
        (PARENS ∘g id ,⊗ DONE ,⊗ id)
        (PARENS ∘g id ,⊗ ATOM*→EXP ,⊗ id)
      ∘g ⊗⊕-distL
      ∘g id ,⊗ ⊗⊕-distR
      ∘g lowerG ,⊗ lowerG ,⊗ lowerG

  unrollEXP : EXP ⊢ ATOM ⊕ (ATOM ⊗ (＂ + ＂ ⊗ ATOM) *)
  unrollEXP = rec BinOpTy unrollEXPAlg Exp

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
    closeBad : b Eq.≡ false → n Eq.≡ 0 → AutomatonTag b n Closing
    unexpectedC : b Eq.≡ false → UnexpectedClosing → AutomatonTag b n Closing

    doneGood : n Eq.≡ 0 → b Eq.≡ true → AutomatonTag b n Adding
    doneBad : ∀ n-1 → n Eq.≡ suc n-1 → b Eq.≡ false → AutomatonTag b n Adding
    add : AutomatonTag b n Adding
    unexpectedA : b Eq.≡ false → UnexpectedAdding → AutomatonTag b n Adding

  DoneOpeningFun : Bool → ℕ → Guard → Functor (ℕ × AutomatonState)
  DoneOpeningFun b n g =
    &e Bool λ where
      true → k (guard g)
      false → Var (n , (Guard→State g))

  DoneOpening : Bool → ℕ → Functor (ℕ × AutomatonState)
  DoneOpening b n = ⊕e Guard (DoneOpeningFun b n)

  mapFalseWithBool : {ℓA : Level} →
    {A B C : Grammar ℓA} →
    B ⊢ C →
    &ᴰ {X = Bool} (λ {true → A ; false → B}) ⊢ &ᴰ {X = Bool} (λ {true → A ; false → C})
  mapFalseWithBool e =
    &ᴰ-intro λ where
      true → π true
      false → e ∘g π false

  -- mapDoneOpening : (b : Bool) → (n : ℕ) → (g : Guard) →
  --   {A B : ℕ × AutomatonState → Grammar ℓ-zero} →
  --   (e : ∀ q → A q ⊢ B q) →
  --   ⟦ DoneOpeningFun b n g ⟧ A ⊢ ⟦ DoneOpeningFun b n g ⟧ B
  -- mapDoneOpening b n g e =
  --   &ᴰ-in λ where
  --     true → &ᴰ-π true
  --     false → liftG ∘g e (n , Guard→State g) ∘g lowerG ∘g &ᴰ-π false

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
        (closeBad Eq.refl Eq.refl) → k (＂ ] ＂ ⊗ ⊤)
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

  -- DoneOpeningClosing : Bool → ℕ → Grammar ℓ-zero
  -- DoneOpeningClosing b n = μ (λ (n , s) → DoneOpeningFun b n ]) (n , Closing)

  -- DoneOpeningAdding : Bool → ℕ → Grammar ℓ-zero
  -- DoneOpeningAdding b n = μ (λ (n , s) → DoneOpeningFun b n ¬]) (n , Adding)

  -- DoneOpeningG : Bool → ℕ → Grammar ℓ-zero
  -- DoneOpeningG b n = DoneOpeningClosing b n ⊕ DoneOpeningAdding b n

  -- After peeking, we choose a subsequent Guard and
  -- AutomatonState to transition to
  -- Here we ensure that the chosen guard and state match
  -- the ones prescribed by DoneOpening
  mkGuardPfs' : ∀ (b : Bool) → (n : ℕ) →
    (tok? : Maybe Tok) →
    AutomatonG  b (n , (Guard→State (Tok→Guard tok?)))
      & Peek tok? ⊢
      ⟦ DoneOpeningFun b n (Tok→Guard tok?) ⟧
        (λ (n , s) → AutomatonG b (n , s))
  mkGuardPfs' b n nothing = &ᴰ-intro λ where
      false → liftG ∘g π₁
      true → liftG ∘g inl ∘g π₂
  mkGuardPfs' b n (just [) = &ᴰ-intro λ where
      false → liftG ∘g π₁
      true → liftG ∘g inr ∘g σ [ ∘g id ,⊗ ⊤-intro ∘g π₂
  mkGuardPfs' b n (just ]) = &ᴰ-intro λ where
      false → liftG ∘g π₁
      true → liftG ∘g id ,⊗ ⊤-intro ∘g π₂
  mkGuardPfs' b n (just +) = &ᴰ-intro λ where
      false → liftG ∘g π₁
      true → liftG ∘g inr ∘g σ NotRP.+ ∘g id ,⊗ ⊤-intro ∘g π₂
  mkGuardPfs' b n (just (num m)) = &ᴰ-intro λ where
      false → liftG ∘g π₁
      true → liftG ∘g inr ∘g σ (num m) ∘g id ,⊗ ⊤-intro ∘g π₂

  -- Whenever we want to use a Guard, this cuts out
  -- the redundant work in checking the guardedness condition
  mkGuardPfs : (n : ℕ) →
    &[ nq ∈ ℕ × AutomatonState ] ⊕[ b ∈ Bool ] AutomatonG b nq
    ⊢
    ⊕[ b ∈ Bool ] ⊕[ g ∈ Guard ] ⟦ DoneOpeningFun b n g ⟧ (AutomatonG b)
  mkGuardPfs n =
    ⊕ᴰ-elim (λ tok? →
      map⊕ᴰ (λ b → σ (Tok→Guard tok?) ∘g mkGuardPfs' b n tok?)
      ∘g &⊕ᴰ-distL≅ .fun ∘g π (n , Guard→State (Tok→Guard tok?)) ,&p id)
    ∘g peek .fun

  forgetGuard : (b : Bool) → (n : ℕ) → (g : Guard) →
    ⟦ DoneOpeningFun b n g ⟧ (AutomatonG b) ⊢ AutomatonG b (n , Guard→State g)
  forgetGuard b n ] = lowerG ∘g π false
  forgetGuard b n ¬] = lowerG ∘g π false

  parse : string ⊢
    &[ nq ∈ ℕ × AutomatonState ]
    ⊕[ b ∈ Bool ]
    AutomatonG b nq
  parse = fold*r _
    -- nil
    ((&ᴰ-intro λ where
      (n , Opening) → σ false ∘g roll ∘g σ (unexpectedO Eq.refl EOF)
      (n , Closing) → σ false ∘g roll ∘g σ (unexpectedC Eq.refl EOF)
      (zero , Adding) → σ true ∘g roll ∘g σ (doneGood Eq.refl Eq.refl)
      (suc n-1 , Adding) → σ false ∘g roll ∘g σ (doneBad n-1 Eq.refl Eq.refl))
      ∘g liftG)
    -- cons
    ((&ᴰ-intro λ where
      (n , Opening) → ⊕ᴰ-elim λ where
        [ → map⊕ᴰ (λ _ → roll ∘g σ left ∘g liftG ,⊗ liftG)
            ∘g ⊕ᴰ-distR .fun
           ∘g id ,⊗ π (suc n , Opening)
        ] → σ false ∘g roll ∘g σ (unexpectedO Eq.refl ]) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → σ false ∘g roll ∘g σ (unexpectedO Eq.refl +) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) →
          map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
          ∘g ⊕ᴰ-distR .fun
          ∘g (σ x) ,⊗ mkGuardPfs n
      (zero , Closing) →
        ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → σ false ∘g roll ∘g σ (closeBad Eq.refl Eq.refl) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → σ false ∘g roll ∘g σ (unexpectedC Eq.refl UnexpectedClosing.+) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) → σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum) ∘g liftG ∘g σ x  ,⊗ ⊤-intro
      (suc n-1 , Closing) →
        ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → map⊕ᴰ (λ _ → roll ∘g σ (closeGood n-1 Eq.refl) ∘g liftG ,⊗ id)
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ mkGuardPfs n-1
        + → σ false ∘g roll ∘g σ (unexpectedC Eq.refl UnexpectedClosing.+) ∘g liftG ∘g id ,⊗ ⊤-intro
        (num x) → σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum) ∘g liftG ∘g σ x  ,⊗ ⊤-intro
      (n , Adding) → ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedA Eq.refl [) ∘g liftG ∘g id ,⊗ ⊤-intro
        ] → σ false ∘g roll ∘g σ (unexpectedA Eq.refl ]) ∘g liftG ∘g id ,⊗ ⊤-intro
        + → map⊕ᴰ (λ _ → roll ∘g σ add ∘g liftG ,⊗ liftG)
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ π (n , Opening)
        (num x) → σ false ∘g roll ∘g σ (unexpectedA Eq.refl aNum) ∘g liftG ∘g (σ x) ,⊗ ⊤-intro )
      ∘g ⊕ᴰ-distL .fun
      )

  printAlg : (b : Bool) →
    Algebra (AutomatonTy' b) (λ _ → string)
  printAlg b (n , Opening) =
    ⊕ᴰ-elim λ where
      left →
        CONS
        ∘g literal→char [ ,⊗ id
        ∘g lowerG ,⊗ lowerG
      num →
        ⊕ᴰ-elim (λ _ → CONS ∘g ⊕ᴰ-elim (literal→char ∘ num) ,⊗ (lowerG ∘g π false))
        ∘g ⊕ᴰ-distR .fun
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
        ⊕ᴰ-elim (λ _ → CONS ∘g literal→char ] ,⊗ (lowerG ∘g π false))
        ∘g ⊕ᴰ-distR .fun
        ∘g lowerG ,⊗ id
      (closeBad Eq.refl Eq.refl) →
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

--   Trace≅string :
--     (n : ℕ) → (s : AutomatonState) →
--     (⊕[ b ∈ Bool ] AutomatonG b (n , s)) ≅ string
--   Trace≅string n s .fun = ⊕ᴰ-elim (λ b → print b n s)
--   Trace≅string n s .inv = &ᴰ-π (n , s) ∘g parse
--   Trace≅string n s .sec = unambiguous-string _ _
--   Trace≅string n s .ret = the-ret
--     where
--     opaque
--       unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
--       {--
--       -- For speed of typechecking it is crucial to separate the equality
--       -- proofs into lemmas. It is also important to scaffold typechecking
--       -- by limiting inference for the signatures of these lemmas
--       --}

--       {--
--       -- Convenient definitions to use in the type signatures of the equality lemmas
--       --}
--       module _ where
--         goal : ℕ → AutomatonState → Grammar ℓ-zero
--         goal n s = ⊕[ b ∈ Bool ] AutomatonG b (n , s)

--         l : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
--           AutomatonG b (n , s) ⊢ goal n s
--         l b n s = &ᴰ-π (n , s) ∘g parse ∘g print b n s

--         r : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
--           AutomatonG b (n , s) ⊢ goal n s
--         r b n s = ⊕ᴰ-in b

--         the-eq : Bool → ℕ × AutomatonState → Grammar ℓ-zero
--         the-eq b (n , s) = equalizer (l b n s) (r b n s)

--         the-eq-π : (b : Bool) → ((n , s) : ℕ × AutomatonState) → equalizer (l b n s) (r b n s) ⊢ AutomatonG b (n , s)
--         the-eq-π b (n , s) = eq-π (l b n s) (r b n s)

--         the-eq-π-pf : (b : Bool) → ((n , s) : ℕ × AutomatonState) →
--           l b n s ∘g the-eq-π b (n , s) ≡ r b n s ∘g the-eq-π b (n , s)
--         the-eq-π-pf b (n , s) = eq-π-pf (l b n s) (r b n s)

--         L : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
--           ⟦ AutomatonTy b n s ⟧ (the-eq b) ⊢ goal n s
--         L b n s = l b n s ∘g roll ∘g map (AutomatonTy' b (n , s)) (the-eq-π b)


--         R : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
--           ⟦ AutomatonTy b n s ⟧ (the-eq b) ⊢ goal n s
--         R b n s = r b n s ∘g roll ∘g map (AutomatonTy' b (n , s)) (the-eq-π b)

--         the-≡-ty : (b : Bool) → (n : ℕ) → (s : AutomatonState) → Type ℓ-zero
--         the-≡-ty b n s = L b n s ≡ R b n s

--         mk≡Ty : {A : Grammar ℓ-zero} →
--           (b : Bool) → (n : ℕ) → (s : AutomatonState) →
--           A ⊢ ⟦ AutomatonTy b n s ⟧ (the-eq b) → Type ℓ-zero
--         mk≡Ty b n s f = L b n s ∘g f ≡ R b n s ∘g f

--       Opening≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Opening
--       Opening≡ b n =
--         ⊕ᴰ≡ _ _ λ where
--         left → the-left-pf
--         num → the-num-pf
--         (unexpectedO Eq.refl c) → the-unexpected-pf c
--           where
--           the-left-pf : mk≡Ty b n Opening (⊕ᴰ-in left)
--           the-left-pf i =
--             map⊕ᴰ (λ b → roll ∘g ⊕ᴰ-in left ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun
--             ∘g id ,⊗ eq-π-pf (l b (suc n) Opening) (r b (suc n) Opening) i ∘g lowerG ,⊗ lowerG

--           the-]-pf' : (m : ℕ) → mk≡Ty b n Opening (⊕ᴰ-in num ∘g liftG ,⊗ ⊕ᴰ-in ] ∘g ⊕ᴰ-in m ,⊗ id)
--           the-]-pf' m =
--             &ᴰ-π (n , Opening)
--             ∘g parse
--             ∘g print b n Opening
--             ∘g roll ∘g ⊕ᴰ-in num
--             ∘g (liftG ∘g ⊕ᴰ-in m) ,⊗ ⊕ᴰ-in ]
--             ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--             --   ≡⟨ refl ⟩
--             -- map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id)
--             -- ∘g ⊕ᴰ-distR .fun
--             -- ∘g (⊕ᴰ-in m) ,⊗
--             --      (⊕ᴰ-elim (λ tok? →
--             --        map⊕ᴰ (λ b → ⊕ᴰ-in (Tok→Guard tok?) ∘g mkGuardPfs' b n tok?)
--             --        ∘g &⊕ᴰ-distL≅ .fun ∘g &ᴰ-π (n , Guard→State (Tok→Guard tok?)) ,&p id))
--             -- ∘g id ,⊗ peek .fun
--             -- ∘g id ,⊗ (parse ∘g print b n Closing ∘g lowerG ∘g &ᴰ-π false)
--             -- ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--               ≡⟨ refl ⟩
--             map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id)
--             ∘g ⊕ᴰ-distR .fun
--             ∘g (⊕ᴰ-in m) ,⊗
--                  (⊕ᴰ-elim (λ tok? →
--                    map⊕ᴰ (λ b → ⊕ᴰ-in (Tok→Guard tok?) ∘g mkGuardPfs' b n tok?)
--                    ∘g &⊕ᴰ-distL≅ .fun ∘g &ᴰ-π (n , Guard→State (Tok→Guard tok?)) ,&p id))
--             -- ∘g id ,⊗ map&ᴰ (λ _ → lowerG)
--             ∘g id ,⊗ peek .fun
--             ∘g id ,⊗ (&ᴰ-π false ∘g mapFalseWithBool (parse ∘g print b n Closing) )
--             -- ∘g id ,⊗ (&ᴰ-π false ∘g mapDoneOpening b n ] (λ (n , s) → parse ∘g print b n s))
--             ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--               ≡⟨ {!!} ⟩
--             ⊕ᴰ-in b
--             ∘g roll ∘g ⊕ᴰ-in num
--             ∘g (liftG ∘g ⊕ᴰ-in m) ,⊗ ⊕ᴰ-in ]
--             ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--           --     -- ≡⟨ refl ⟩
--           --   -- map⊕ᴰ (λ _ →
--           --   --   roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id
--           --   --   ∘g ⊕ᴰ-in m ,⊗ ⊕ᴰ-in ]
--           --   --   )
--           --   -- ∘g ⊕ᴰ-in b
--           --   -- ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--             ∎

--           -- the-]-pf : mk≡Ty b n Opening (⊕ᴰ-in num ∘g liftG ,⊗ ⊕ᴰ-in ])
--           -- the-]-pf =
--           --   &ᴰ-π (n , Opening)
--           --   ∘g parse
--           --   ∘g print b n Opening
--           --   ∘g roll ∘g ⊕ᴰ-in num
--           --   ∘g liftG ,⊗ ⊕ᴰ-in ]
--           --   ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--           --     ≡⟨ refl ⟩
--           --   -- map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in num ∘g liftG ,⊗ id)
--           --   -- ∘g ⊕ᴰ-distR .fun
--           --   -- ∘g id ,⊗ mkGuardPfs n
--           --   --
--           --   -- (
--           --   --   ⊕ᴰ-elim (λ tok? →
--           --   --     map⊕ᴰ (λ b → ⊕ᴰ-in (Tok→Guard tok?) ∘g mkGuardPfs' b n tok?)
--           --   --     ∘g &⊕ᴰ-distL≅ .fun ∘g &ᴰ-π (n , Guard→State (Tok→Guard tok?)) ,&p id)
--           --   --   ∘g peek .fun
--           --   --   )
--           --   --
--           --   ⊕ᴰ-elim (λ m →
--           --   &ᴰ-π (n , Opening)
--           --   ∘g parse
--           --   ∘g CONS
--           --   ∘g ⊕ᴰ-elim (literal→char ∘ num) ,⊗ id
--           --   )
--           --   ∘g id ,⊗ (print b n Closing ∘g lowerG ∘g &ᴰ-π false)
--           --   ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--           --     ≡⟨ {!!} ⟩
--           --   ⊕ᴰ-in b
--           --   ∘g roll ∘g ⊕ᴰ-in num
--           --   ∘g liftG ,⊗ ⊕ᴰ-in ]
--           --   ∘g id ,⊗ map (DoneOpeningFun b n ]) (the-eq-π b)
--           --   ∎

--           the-¬]-pf : mk≡Ty b n Opening (⊕ᴰ-in num ∘g liftG ,⊗ ⊕ᴰ-in ¬])
--           the-¬]-pf = {!!}

--           -- the-guard-pf :
--           --   (g : Guard) →
--           --   mk≡Ty b n Opening (⊕ᴰ-in num ∘g liftG ,⊗ ⊕ᴰ-in g)
--           -- the-guard-pf ] = {!!}
--           -- the-guard-pf ¬] = ?

--           the-num-pf : mk≡Ty b n Opening (⊕ᴰ-in num)
--           the-num-pf = {!!}

--           the-unexpected]-pf :
--             mk≡Ty false n Opening (⊕ᴰ-in (unexpectedO Eq.refl ]))
--           the-unexpected]-pf =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl ]) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)

--           the-unexpected+-pf :
--             mk≡Ty false n Opening (⊕ᴰ-in (unexpectedO Eq.refl +))
--           the-unexpected+-pf =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedO Eq.refl +) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)

--           the-unexpected-pf :
--             (c : UnexpectedOpening) →
--             mk≡Ty false n Opening (⊕ᴰ-in (unexpectedO Eq.refl c))
--           the-unexpected-pf EOF = refl
--           the-unexpected-pf ] = the-unexpected]-pf
--           the-unexpected-pf + = the-unexpected+-pf

--       unexpectedClosing≡ :
--         (n : ℕ) →
--         (c : UnexpectedClosing) →
--         mk≡Ty false n Closing (⊕ᴰ-in (unexpectedC Eq.refl c))
--       unexpectedClosing≡ n EOF = refl
--       unexpectedClosing≡ zero [ =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)
--       unexpectedClosing≡ (suc n) [ =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)
--       unexpectedClosing≡ zero + =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl +) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)
--       unexpectedClosing≡ (suc n) + =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl +) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)
--       unexpectedClosing≡ zero aNum =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl aNum) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)
--       unexpectedClosing≡ (suc n) aNum =
--         cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedC Eq.refl aNum) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--           (unambiguous⊤ _ _)

--       Closing≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Closing
--       Closing≡ b zero = ⊕ᴰ≡ _ _ λ where
--         (closeBad Eq.refl Eq.refl) → the-close-bad-pf
--         (unexpectedC Eq.refl c) → unexpectedClosing≡ zero c
--           where
--           the-close-bad-pf : mk≡Ty false 0 Closing (⊕ᴰ-in (closeBad Eq.refl Eq.refl))
--           the-close-bad-pf =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (closeBad Eq.refl Eq.refl) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)
--       Closing≡ b (suc n) = ⊕ᴰ≡ _ _ λ where
--         (closeGood n-1 Eq.refl) → the-close-good-pf n-1
--         (unexpectedC Eq.refl c) → unexpectedClosing≡ (suc n) c
--           where
--           the-]-pf : (n-1 : ℕ) → mk≡Ty b (suc n-1) Closing (⊕ᴰ-in (closeGood n-1 Eq.refl) ∘g liftG ,⊗ ⊕ᴰ-in ])
--           the-]-pf = {!!}

--           the-¬]-pf : (n-1 : ℕ) → mk≡Ty b (suc n-1) Closing (⊕ᴰ-in (closeGood n-1 Eq.refl) ∘g liftG ,⊗ ⊕ᴰ-in ¬])
--           the-¬]-pf = {!!}

--           the-guard-pf :
--             (n-1 : ℕ) →
--             (g : Guard) →
--             mk≡Ty b (suc n-1) Closing (⊕ᴰ-in (closeGood n-1 Eq.refl) ∘g liftG ,⊗ ⊕ᴰ-in g)
--           the-guard-pf n-1 ] = the-]-pf n-1
--           the-guard-pf n-1 ¬] = the-¬]-pf n-1

--           the-close-good-pf :
--             (n-1 : ℕ) →
--             mk≡Ty b (suc n-1) Closing (⊕ᴰ-in (closeGood n-1 Eq.refl))
--           the-close-good-pf n-1 i = ⊕ᴰ-elim (λ g → the-guard-pf n-1 g i) ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ id

--       Adding≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Adding
--       Adding≡ b n = ⊕ᴰ≡ _ _ λ where
--         (doneGood Eq.refl Eq.refl) → refl
--         (doneBad n-1 Eq.refl Eq.refl) → refl
--         add → the-add-pf
--         (unexpectedA Eq.refl c) → the-unexpected-pf c
--           where
--           the-add-pf : mk≡Ty b n Adding (⊕ᴰ-in add)
--           the-add-pf i =
--             map⊕ᴰ (λ _ → roll ∘g ⊕ᴰ-in add ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun
--             ∘g id ,⊗ eq-π-pf (l b n Opening) (r b n Opening) i ∘g lowerG ,⊗ lowerG

--           the-unexpected-pf :
--             (c : UnexpectedAdding) →
--             mk≡Ty false n Adding (⊕ᴰ-in (unexpectedA Eq.refl c))
--           the-unexpected-pf [ =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl [) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)
--           the-unexpected-pf ] =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl ]) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)
--           the-unexpected-pf aNum =
--             cong (λ z → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in (unexpectedA Eq.refl aNum) ∘g liftG ∘g id ,⊗ z ∘g lowerG)
--               (unambiguous⊤ _ _)

--       the-ret : &ᴰ-π (n , s) ∘g parse ∘g ⊕ᴰ-elim (λ b → print b n s) ≡ id
--       the-ret = ⊕ᴰ≡ _ _ λ b →
--         equalizer-ind
--           (AutomatonTy' b)
--           (λ (n , s) → ⊕[ b ∈ Bool ] AutomatonG b (n , s))
--           (λ (n , s) → &ᴰ-π (n , s) ∘g parse ∘g print b n s)
--           (λ (n , s) → ⊕ᴰ-in b)
--           (λ where
--             (n , Opening) → Opening≡ b n
--             (n , Closing) → Closing≡ b n
--             (n , Adding) → Adding≡ b n
--           )
--           (n , s)

-- -- Soundness : from every trace we can extract an LL⟨1⟩ parse
-- module Soundness where
--   open LL⟨1⟩
--   open Automaton

--   Stk : ℕ → Grammar ℓ-zero
--   Stk zero = ε
--   Stk (suc n) = ＂ ] ＂ ⊗ (＂ + ＂ ⊗ ATOM) * ⊗ Stk n

--   ⟦_⟧State : ℕ × AutomatonState → Grammar ℓ-zero
--   ⟦ n , Opening ⟧State = EXP ⊗ Stk n
--   ⟦ n , Closing ⟧State = Stk n
--   ⟦ n , Adding ⟧State = (＂ + ＂ ⊗ ATOM) * ⊗ Stk n

--   buildExpAlg : Algebra (AutomatonTy' true) ⟦_⟧State
--   buildExpAlg (n , Opening) =
--     ⊕ᴰ-elim λ where
--       left → ATOM*→EXP ,⊗ id ∘g ⊗-assoc ∘g ⊸3⊗ (⊸3-intro-ε PARENS) ∘g lowerG ,⊗ lowerG
--       num →
--         (⊕ᴰ-elim λ where
--           ] → (DONE ∘g NUM) ,⊗ id ∘g id ,⊗ (lowerG ∘g &ᴰ-π false)
--           ¬] → (ATOM*→EXP ∘g NUM ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ (lowerG ∘g &ᴰ-π false)
--         )
--         ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ id
--   buildExpAlg (n , Closing) =
--     ⊕ᴰ-elim λ where
--       (closeGood n-1 Eq.refl) →
--         (⊕ᴰ-elim λ where
--           ] →
--             id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻) ∘g id ,⊗ (lowerG ∘g &ᴰ-π false)
--           ¬] → id ,⊗ (lowerG ∘g &ᴰ-π false)
--         )
--         ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ id
--   buildExpAlg (n , Adding) =
--     ⊕ᴰ-elim λ where
--       (doneGood Eq.refl Eq.refl) → NIL ,⊗ id ∘g ⊗-unit-r⁻ ∘g lowerG
--       add →
--         ⊕-elim
--           (*-singleton _ ,⊗ id ∘g ⊗-assoc)
--           ((CONS ∘g ⊗-assoc) ,⊗ id ∘g ⊗-assoc)
--         ∘g ⊗⊕-distL
--         ∘g id ,⊗ (⊗⊕-distR ∘g unrollEXP ,⊗ id)
--         ∘g lowerG ,⊗ lowerG

--   buildExp : AutomatonG true (0 , Opening) ⊢ EXP
--   buildExp = ⊗-unit-r ∘g rec _ buildExpAlg (0 , Opening)

-- -- Completeness : every LL⟨1⟩ parse has a corresponding accepting trace
-- -- module Completeness where
-- --   open LL⟨1⟩
-- --   open Automaton

-- -- -- TODO : its not clear how to make a DoneOpening grammar
-- --   ⟦_⟧Nonterminal : Nonterminal → Grammar ℓ-zero
-- --   ⟦ Exp ⟧Nonterminal = &[ n ∈ ℕ ] {!!} -- &[ n ∈ ℕ ] (DoneOpeningG true n ⊸ AutomatonG true (n , Opening))
-- --   ⟦ Atom ⟧Nonterminal = {!!} -- &[ n ∈ ℕ ] (DoneOpeningG true n ⊸ AutomatonG true (n , Opening))

--   -- mkTraceAlg : Algebra BinOpTy ⟦_⟧Nonterminal
--   -- mkTraceAlg Exp =
--   --   ⊕ᴰ-elim λ where
--   --     done →
--   --       id
--   --       ∘g lowerG
--   --     add → {!!}
--   -- mkTraceAlg Atom =
--   --   ⊕ᴰ-elim λ where
--   --     num → {!!}
--   --     parens → {!!}

--   -- mkTrace : EXP ⊢ AutomatonG true (0 , Opening)
--   -- mkTrace =
--   --   ⊸-app
--   --   ∘g id ,⊗ {!!}
--   --   ∘g ⊗-unit-r⁻
--   --   ∘g &ᴰ-π 0
--   --   ∘g rec _ mkTraceAlg Exp

-- -- -- {- Grammar for one associative binary operation with constants and parens -}
-- -- -- {-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- -- -- module Examples.BinOp where

-- -- -- open import Cubical.Foundations.Prelude
-- -- -- open import Cubical.Foundations.Equiv
-- -- -- open import Cubical.Foundations.Isomorphism
-- -- -- open import Cubical.Foundations.Function
-- -- -- open import Cubical.Foundations.HLevels

-- -- -- open import Cubical.Data.Bool hiding (_⊕_)
-- -- -- open import Cubical.Data.Maybe as Maybe
-- -- -- open import Cubical.Data.Nat as Nat
-- -- -- open import Cubical.Data.FinSet
-- -- -- open import Cubical.Data.Sum as Sum
-- -- -- open import Cubical.Data.Sigma

-- -- -- -- TODO need to make this work with opaqueness
-- -- -- -- data Tok : Type where
-- -- -- --   LP RP : Tok   -- parens
-- -- -- --   * : Tok       -- the binary operation
-- -- -- --   num : ℕ → Tok -- constants

-- -- -- -- Alphabet : hSet _
-- -- -- -- Alphabet = Tok , isSetRetract encode decode dex≡x (isSet⊎ isSetFin isSetℕ)
-- -- -- --   where
-- -- -- --   open import Cubical.Data.Sum as Sum
-- -- -- --   open import Cubical.Data.Fin as Fin
-- -- -- --   Tok' = Fin 3 ⊎ ℕ
-- -- -- --   encode : Tok → Tok'
-- -- -- --   encode LP = inl 0
-- -- -- --   encode RP = inl 1
-- -- -- --   encode * = inl 2
-- -- -- --   encode (num x) = inr x
-- -- -- --   decode : Tok' → Tok
-- -- -- --   decode (inl (0 , snd₁)) = LP
-- -- -- --   decode (inl (1 , snd₁)) = RP
-- -- -- --   decode (inl (suc (suc fst₁) , snd₁)) = *
-- -- -- --   decode (inr x) = num x
-- -- -- --   dex≡x : ∀ x → decode (encode x) ≡ x
-- -- -- --   dex≡x LP = refl
-- -- -- --   dex≡x RP = refl
-- -- -- --   dex≡x * = refl
-- -- -- --   dex≡x (num x) = refl

-- -- -- -- open import Grammar Alphabet
-- -- -- -- open import Grammar.Equivalence Alphabet
-- -- -- -- open import Term Alphabet

-- -- -- -- anyNum : Grammar _
-- -- -- -- anyNum = LinΣ[ n ∈ ℕ ] literal (num n)
-- -- -- -- module LL⟨1⟩ where
-- -- -- --   Exp : Grammar ℓ-zero
-- -- -- --   data Atom : Grammar ℓ-zero

-- -- -- --   Exp = Atom ⊗' (KL* (literal * ⊗' Atom))
-- -- -- --   data Atom where
-- -- -- --     num : ∀ {n} → literal (num n) ⊢ Atom
-- -- -- --     parens :
-- -- -- --       literal LP ⊗' Exp ⊗' literal RP ⊢ Atom

-- -- -- --   -- This grammar is LL(1) because after you match a close paren, you
-- -- -- --   -- need to look ahead one token to know if you continue matching
-- -- -- --   -- close parens or have finished parsing the Atom.
-- -- -- --   opaque
-- -- -- --     unfolding _⊗_
-- -- -- --     num' : ∀ {n} → ε ⊢ Atom ⊸ literal (num n)
-- -- -- --     num' {n} = ⊸-intro-ε {k = Atom} (num {n})
-- -- -- --     parens' : ε ⊢ Atom ⊸ literal RP ⊸ Exp ⊸ literal LP
-- -- -- --     parens' = ⊸3-intro-ε parens

-- -- -- --   record Algebra ℓ : Type (ℓ-suc ℓ) where
-- -- -- --     field
-- -- -- --       UE : Grammar ℓ
-- -- -- --       UAs : Grammar ℓ
-- -- -- --       UA : Grammar ℓ

-- -- -- --       [mkExp] : UA ⊗ UAs ⊢ UE
-- -- -- --       [nil] : ε ⊢ UAs
-- -- -- --       [cons] : (literal * ⊗ UA) ⊗ UAs ⊢ UAs
-- -- -- --       [num] : ∀ {n} → literal (num n) ⊢ UA
-- -- -- --       [parens] : literal LP ⊗ UE ⊗ literal RP ⊢ UA

-- -- -- --   open Algebra
-- -- -- --   opaque
-- -- -- --     unfolding _⊗_
-- -- -- --     initialAlgebra : Algebra ℓ-zero
-- -- -- --     initialAlgebra .UE = Exp
-- -- -- --     initialAlgebra .UAs = KL* (literal * ⊗ Atom)
-- -- -- --     initialAlgebra .UA = Atom
-- -- -- --     initialAlgebra .[mkExp] = id
-- -- -- --     initialAlgebra .[nil] = nil
-- -- -- --     initialAlgebra .[cons] = cons
-- -- -- --     initialAlgebra .[num] = num
-- -- -- --     initialAlgebra .[parens] = parens
-- -- -- --   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- --     field
-- -- -- --       fE : A .UE ⊢ B .UE
-- -- -- --       fAs : A .UAs ⊢ B .UAs
-- -- -- --       fA : A .UA ⊢ B .UA

-- -- -- --   -- this can be avoided by doing manual recursion for rAs
-- -- -- --   opaque
-- -- -- --     unfolding _⊗_ initialAlgebra
-- -- -- --     fold : ∀ {ℓ}(A : Algebra ℓ) → Hom initialAlgebra A
-- -- -- --     fold A = record { fE = rE ; fAs = rAs ; fA = rA } where
-- -- -- --       rE : Exp ⊢ A .UE
-- -- -- --       rAs : KL* (literal * ⊗ Atom) ⊢ A .UAs
-- -- -- --       rA : Atom ⊢ A .UA
-- -- -- --       rE _ (sp , a , as) = A .[mkExp] _ (sp , rA _ a , rAs _ as)
-- -- -- --       rAs _ (KL*.nil _ x) = A .[nil] _ x
-- -- -- --       rAs _ (KL*.cons _ (sp1 , (sp2 , star , a) , as)) = A .[cons] _ (sp1 , (sp2 , star , rA _ a) , rAs _ as)
-- -- -- --       rA _ (num _ x) = A .[num] _ x
-- -- -- --       rA _ (parens _ (sp1 , lp , sp2 , e , rp)) = A .[parens] _ (sp1 , lp , sp2 , rE _ e , rp)

-- -- -- -- module Automaton where
-- -- -- --   -- TODO: we should be able to generalize this definition to an
-- -- -- --   -- (infinite state) deterministic automaton with guarded
-- -- -- --   -- transitions.

-- -- -- --   -- the stack is a number,
-- -- -- --   -- the number of open parens that are closed by the term

-- -- -- --   -- Exp is for when we are parsing a single expression, Suffix is
-- -- -- --   -- when we are parsing the sequence of multiplications after an
-- -- -- --   -- expression

-- -- -- --   -- the boolean is whether it is an accepting or rejecting trace

-- -- -- --   -- three cases: Opening, Closing, Multiplying

-- -- -- --   -- Opening: at the start of an expression, the term starts with a
-- -- -- --   -- sequence of 0 or more opening parens, which we count. Ends when
-- -- -- --   -- we see a number, then we use lookahead to determine whether to
-- -- -- --   -- parse closing parens or start parsing a multiplication sequence
-- -- -- --   data Opening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- -- -- --   -- Closing: parse as many closing parens as you can, eventually
-- -- -- --   -- use lookahead to decide when to start parsing multiplication sequence
-- -- -- --   data Closing : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- -- -- --   -- Parse a sequence of * Exps
-- -- -- --   data Multiplying : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- -- -- --   DoneOpening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
-- -- -- --   DoneOpening n b =
-- -- -- --     ((ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤) &' Multiplying n b)
-- -- -- --     ⊕' ((literal RP ⊗' ⊤) &' Closing n b)
-- -- -- --   data Opening where
-- -- -- --     left : ∀ {n b} → literal LP ⊗' Opening (suc n) b ⊢ Opening n b
-- -- -- --     num  : ∀ {n b} →
-- -- -- --       (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗' DoneOpening n b ⊢ Opening n b
-- -- -- --     unexpected : ∀ {n} → ε ⊕' (literal RP ⊕' literal *) ⊗' ⊤ ⊢ Opening n false

-- -- -- --   data Closing where
-- -- -- --     rightClose : ∀ {n b} →
-- -- -- --       literal RP ⊗' DoneOpening n b ⊢ Closing (suc n) b
-- -- -- --     rightUnmatched : literal RP ⊗' ⊤ ⊢ Closing 0 false
-- -- -- --     unexpected : ∀ {n} → ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤ ⊢ Closing n false

-- -- -- --   data Multiplying where
-- -- -- --     done : ε ⊢ Multiplying 0 true
-- -- -- --     times : ∀ {n b} → literal * ⊗' Opening n b ⊢ Multiplying n b
-- -- -- --     unmatched : ∀ {n} → ε ⊢ Multiplying (suc n) false
-- -- -- --     unexpected : ∀ {n} →
-- -- -- --       (literal LP ⊕' literal RP ⊕' anyNum) ⊗' ⊤ ⊢ Multiplying n false

-- -- -- --   -- note this is for the true cases, the tautological one would also
-- -- -- --   -- have false cases but we would just use ⊥ for them.
-- -- -- --   --
-- -- -- --   -- because of this we are getting a `warning: -W[no]UnsupportedIndexedMatch`
-- -- -- --   record Algebra ℓ : Type (ℓ-suc ℓ) where
-- -- -- --     field
-- -- -- --       UO : ℕ → Grammar ℓ
-- -- -- --       UC : ℕ → Grammar ℓ
-- -- -- --       UM : ℕ → Grammar ℓ
-- -- -- --     UDO : ℕ → Grammar ℓ
-- -- -- --     UDO n = ((ε ⊕ (literal * ⊕ literal LP ⊕ anyNum) ⊗ ⊤) & UM n)
-- -- -- --       ⊕ ((literal RP ⊗ ⊤) & UC n)
-- -- -- --     field
-- -- -- --       [left] : ∀ {n} → literal LP ⊗ UO (suc n) ⊢ UO n
-- -- -- --       [num]  : ∀ {n} → (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ UDO n ⊢ UO n
-- -- -- --       [rightClose] : ∀ {n} → literal RP ⊗ UDO n ⊢ UC (suc n)
-- -- -- --       [done] : ε ⊢ UM 0
-- -- -- --       [times] : ∀ {n} → literal * ⊗ UO n ⊢ UM n

-- -- -- --   open Algebra
-- -- -- --   opaque
-- -- -- --     unfolding _⊗_ _⊕_ _&_
-- -- -- --     initialAlgebra : Algebra ℓ-zero
-- -- -- --     initialAlgebra .UO n = Opening n true
-- -- -- --     initialAlgebra .UC n = Closing n true
-- -- -- --     initialAlgebra .UM n = Multiplying n true
-- -- -- --     initialAlgebra .[left] = left
-- -- -- --     initialAlgebra .[num] = num
-- -- -- --     initialAlgebra .[rightClose] = rightClose
-- -- -- --     initialAlgebra .[times] = times
-- -- -- --     initialAlgebra .[done] = done

-- -- -- --   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- --     field
-- -- -- --       fO : ∀ n → A .UO n ⊢ B .UO n
-- -- -- --       fC : ∀ n → A .UC n ⊢ B .UC n
-- -- -- --       fM : ∀ n → A .UM n ⊢ B .UM n
-- -- -- --       -- TODO: the equations

-- -- -- --   opaque
-- -- -- --     unfolding _⊗_ _⊕_ _&_ initialAlgebra
-- -- -- --     -- TODO these defs need indexed pattern matching
-- -- -- --     fold : ∀ {ℓ} (A : Algebra ℓ) → Hom initialAlgebra A
-- -- -- --     fold A = record { fO = rO ; fC = rC ; fM = rM } where
-- -- -- --       rO : ∀ n → Opening n true ⊢ A .UO n
-- -- -- --       rC : ∀ n → Closing n true ⊢ A .UC n
-- -- -- --       rM : ∀ n → Multiplying n true ⊢ A .UM n
-- -- -- --       rDO : ∀ n → DoneOpening n true ⊢ UDO A n
-- -- -- --       rO n w (left _ (sp , lp , o)) = A .[left] w (sp , (lp , rO _ _ o))
-- -- -- --       rO n w (num _ (sp , m , doo)) = A .[num] _ (sp , m , rDO _ _ doo)
-- -- -- --       rC _ w (rightClose _ (sp , rp , doo)) = A .[rightClose] _ (sp , rp , rDO _ _ doo)
-- -- -- --       rM _ w (done _ x) = A .[done] _ x
-- -- -- --       rM _ w (times _ (sp , star , o)) = A .[times] _ (sp , star , rO _ _ o)
-- -- -- --       rDO n w (inl x) = inl ((x .fst) , (rM _ _ (x .snd)))
-- -- -- --       rDO n w (inr x) = inr (x .fst , rC _ _ (x .snd))
-- -- -- --     Peek : Maybe Tok → Grammar ℓ-zero
-- -- -- --     Peek = Maybe.rec ε (λ c → literal c ⊗ ⊤)

-- -- -- --     Goal : Grammar ℓ-zero
-- -- -- --     Goal = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- -- -- --       (LinearΣ (Opening n)
-- -- -- --       & LinearΣ (Closing n)
-- -- -- --       & LinearΣ (Multiplying n))

-- -- -- --     -- TODO typechecking this parse term is very slow
-- -- -- --     -- Should probably split it into several pieces
-- -- -- -- --     opaque
-- -- -- -- --       -- unfolding LL⟨1⟩.fold LL⟨1⟩.num' LL⟨1⟩.parens' LL⟨1⟩.initialAlgebra _⊗_ _⊕_ _&_ _⇒_ ⊕-elim ⇒-intro ⇐-intro ⟜-intro ⟜-app ⊸-intro ⊸-app KL*r-elim fold initialAlgebra ⊗-intro &-intro &-π₁ &-π₂ ⊕-inl ⊕-inr ⇒-app
-- -- -- -- --       parse' : string ⊢ LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- -- -- -- --         (LinearΣ (Opening n)
-- -- -- -- --         & LinearΣ (Closing n)
-- -- -- -- --         & LinearΣ (Multiplying n))
-- -- -- -- --       parse' = foldKL*r char
-- -- -- -- --         (record {
-- -- -- -- --           the-ℓ = ℓ-zero
-- -- -- -- --         ; G = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- -- -- -- --               (LinearΣ (Opening n)
-- -- -- -- --               & LinearΣ (Closing n)
-- -- -- -- --               & LinearΣ (Multiplying n))
-- -- -- -- --         ; nil-case =
-- -- -- -- --           LinΣ-intro Maybe.nothing
-- -- -- -- --           ,& LinΠ-intro λ n →
-- -- -- -- --             (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- -- -- --             ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- -- -- --             ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))}
-- -- --                      (LinΣ-intro true ∘g done)
-- -- --                      (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- -- -- -- --         ; cons-case =
-- -- -- -- --           (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- -- -- -- --             (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- -- -- -- --           ,& LinΠ-intro λ n →
-- -- -- -- --             {!!}
-- -- -- -- --         })
-- -- -- -- --       -- foldKL*r _ (record { the-ℓ = _ ; G = _
-- -- -- -- --       --   ; nil-case =
-- -- -- -- --       --     LinΣ-intro Maybe.nothing
-- -- -- -- --       --     ,& LinΠ-intro λ n →
-- -- -- -- --       --     (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- -- -- --       --     ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- -- -- -- --       --     ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- -- -- -- --       --   ; cons-case =
-- -- -- -- --       --     (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- -- -- -- --       --       (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- -- -- -- --       --     ,& LinΠ-intro λ n →
-- -- -- -- --       --       (⊸-intro⁻
-- -- -- -- --       --         (LinΣ-elim λ
-- -- -- -- --       --         { (num x) → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- -- -- --       --           -- goto closing
-- -- -- -- --       --           { (just RP) → ⇒-intro (⇐-intro⁻ (((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- -- -- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ ⊕-inr))) ∘g &-π₁) ∘g &-π₂))
-- -- -- -- --       --           ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- -- -- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --           ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- -- -- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --           ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- -- -- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --           ; (just (num y)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro
-- -- -- {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro y) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --           }))
-- -- -- -- --       --           ∘g id ,⊗ id ,&p LinΠ-app n)
-- -- -- -- --       --           --  (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- -- -- --       --         ; LP → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (((LinΣ-elim (λ b → ⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g left)) ∘g &-π₁)) ∘g LinΠ-app (suc n) ∘g &-π₂))
-- -- -- -- --       --         ; RP → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- -- -- --       --         ; * → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inr ,⊗ ⊤-intro)
-- -- -- -- --       --         })
-- -- -- -- --       --       )
-- -- -- -- --       --       -- ⊸-intro⁻
-- -- -- -- --       --       ,& ⊸-intro⁻ (LinΣ-elim λ
-- -- -- -- --       --        { RP → ⊸-intro {k = LinearΣ (Closing n)} (Nat.elim {A = λ n → Term (literal RP ⊗ Goal) (LinearΣ (Closing n))}
-- -- -- -- --       --          -- empty stack
-- -- -- -- --       --          (LinΣ-intro false ∘g rightUnmatched ∘g id ,⊗ ⊤-intro)
-- -- -- -- --       --          -- popped
-- -- -- -- --       --          (λ n-1 _ → (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- -- -- -- --       --            { (just RP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- -- -- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ ⊕-inr))) ∘g &-π₁ ∘g &-π₂))
-- -- -- -- --       --            ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- -- -- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --            ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- -- -- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --            ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- -- -- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --            ; (just (num x)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)}
-- -- -- (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- -- -- -- --       --            })) ∘g id ,⊗ id ,&p LinΠ-app n-1))
-- -- -- -- --       --          n)
-- -- -- -- --       --        ; LP → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- -- -- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- -- -- -- --       --        ; * → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- -- -- --       --          unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- -- -- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- -- -- -- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro)
-- -- -- -- --       --        })
-- -- -- -- --       --       ,&
-- -- -- -- --       --      (⊸-intro⁻ (LinΣ-elim λ
-- -- -- -- --       --        { * → ⊸-intro {k = LinearΣ (Multiplying n)} (⟜-intro⁻ ((((LinΣ-elim λ b → ⟜-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro b ∘g times)) ∘g &-π₁) ∘g LinΠ-app n) ∘g &-π₂))
-- -- -- -- --       --        ; LP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inl ,⊗ ⊤-intro)
-- -- -- -- --       --        ; RP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- -- -- -- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro) }))
-- -- -- -- --       --   })

-- -- -- -- -- --     parse : string ⊢ LinΣ[ b ∈ Bool ] Opening zero b
-- -- -- -- -- --     parse = ((&-π₁ ∘g LinΠ-app zero) ∘g &-π₂) ∘g parse'

-- -- -- -- -- -- -- Soundness: i.e., that from every trace we can extract an LL(1) parse
-- -- -- -- -- -- module Soundness where
-- -- -- -- -- --   buildExp : Automaton.Opening 0 true ⊢ LL⟨1⟩.Exp
-- -- -- -- -- --   buildExp = ⊗-unit-r ∘g Automaton.Hom.fO (Automaton.fold alg) 0 where
-- -- -- -- -- --     open LL⟨1⟩ using (Exp; Atom)
-- -- -- -- -- --     open Automaton.Algebra
-- -- -- -- -- --     Stk : ℕ → Grammar ℓ-zero
-- -- -- -- -- --     Stk = Nat.elim ε
-- -- -- -- -- --       (λ _ Stk⟨n⟩ → literal RP ⊗ KL* (literal * ⊗ Atom) ⊗ Stk⟨n⟩)
-- -- -- -- -- --     alg : Automaton.Algebra ℓ-zero
-- -- -- -- -- --     alg .UO n = Exp ⊗ Stk n
-- -- -- -- -- --     alg .UC n = Stk n
-- -- -- -- -- --     alg .UM n = KL* (literal * ⊗ Atom) ⊗ Stk n
-- -- -- -- -- --     alg .[left] = ⊗-assoc ∘g ⊸3⊗ LL⟨1⟩.parens'
-- -- -- -- -- --     alg .[num] {n} = ⟜-intro⁻ (⊕-elim
-- -- -- -- -- --       -- the next thing was multiplying
-- -- -- -- -- --       (⟜-intro {k = Exp ⊗ Stk n} (⊗-assoc ∘g (LinΣ-elim λ _ → Atom.num) ,⊗ &-π₂))
-- -- -- -- -- --       -- the next thing was closing
-- -- -- -- -- --       (⟜-intro {k = Exp ⊗ Stk n} ((LinΣ-elim λ _ → Atom.num ,⊗ nil ∘g ⊗-unit-r⁻) ,⊗ &-π₂)))
-- -- -- -- -- --     alg .[rightClose] {n} = ⟜-intro⁻ (⊕-elim
-- -- -- -- -- --       -- next is multiplying
-- -- -- -- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ &-π₂))
-- -- -- -- -- --       -- next is more closing
-- -- -- -- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ (⊸0⊗ nil ∘g &-π₂))))
-- -- -- -- -- --     alg .[times] = ⊸2⊗ cons' ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻
-- -- -- -- -- --     alg .[done] = ⊸0⊗ nil

-- -- -- -- -- -- -- Completeness i.e., that every LL(1) parse has a trace. Though
-- -- -- -- -- -- -- completeness would be that every LL(1) parse corresponds to one we
-- -- -- -- -- -- -- extract from the previous function

-- -- -- -- -- -- -- kind of would want a truly dependent linear type here
-- -- -- -- -- -- -- to formulate it that way...
-- -- -- -- -- -- module Completeness where
-- -- -- -- -- --   open LL⟨1⟩.Hom
-- -- -- -- -- --   mkTrace : LL⟨1⟩.Exp ⊢ Automaton.Opening 0 true
-- -- -- -- -- --   mkTrace = (⊸-app ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,& Automaton.done) ∘g ⊗-unit-r⁻) ∘g LinΠ-app 0 ∘g LL⟨1⟩.fold the-alg .fE where
-- -- -- -- -- --     open LL⟨1⟩.Algebra
-- -- -- -- -- --     the-alg : LL⟨1⟩.Algebra ℓ-zero
-- -- -- -- -- --     -- need to update the motive: a UAs should also produce a proof that it starts with ε or *
-- -- -- -- -- --     the-alg .UE = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- -- -- -- --     the-alg .UAs = LinΠ[ n ∈ ℕ ] (Automaton.DoneOpening n true ⊸ Automaton.DoneOpening n true)
-- -- -- -- -- --     the-alg .UA = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- -- -- -- --     the-alg .[mkExp] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- -- -- --       (((⊸-app ∘g LinΠ-app n ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻))
-- -- -- -- -- --     the-alg .[nil] = LinΠ-intro λ n → ⊸-intro-ε id
-- -- -- -- -- --     the-alg .[cons] = LinΠ-intro λ n → ⊸-intro {k = Automaton.DoneOpening n true}
-- -- -- -- -- --       (((((⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro) ,& Automaton.times) ∘g id ,⊗ ⊸-app) ∘g ⊗-assoc⁻) ∘g (id ,⊗ LinΠ-app n) ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)
-- -- -- -- -- --     the-alg .[num] {m} = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- -- -- --       (Automaton.num ∘g LinΣ-intro m ,⊗ id)
-- -- -- -- -- --     the-alg .[parens] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- -- -- -- --       ((Automaton.left ∘g id ,⊗ (⊸-app {g = Automaton.Opening (suc n) true} ∘g LinΠ-app (suc n) ,⊗ (⊕-inr ∘g (id ,⊗ ⊤-intro) ,& Automaton.rightClose)∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
