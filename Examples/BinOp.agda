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
import Cubical.Data.Empty as Empty
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
        (λ { [ → Sum.inl true ; ] → Sum.inl false
           ; + → Sum.inr (Sum.inl _) ; (num x) → Sum.inr (Sum.inr x)})
        (λ { (Sum.inl false) → ] ; (Sum.inl true) → [ ; (Sum.inr (Sum.inl x)) → +
           ; (Sum.inr (Sum.inr x)) → num x})
        (λ { (Sum.inl false) → refl ; (Sum.inl true) → refl ; (Sum.inr (Sum.inl x)) → refl
           ; (Sum.inr (Sum.inr x)) → refl})
        λ { [ → refl ; ] → refl ; + → refl ; (num x) → refl}

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .leftInv)
      (Sum.isSet⊎ isSetBool (Sum.isSet⊎ isSetUnit isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

+≢[ : Tok.+ Eq.≡ Tok.[ → Empty.⊥
+≢[ ()

+≢] : Tok.+ Eq.≡ Tok.] → Empty.⊥
+≢] ()

+≢num : ∀ x → Tok.+ Eq.≡ Tok.num x → Empty.⊥
+≢num x ()

open import Grammar Alphabet hiding (_+)
import Grammar.Sum.Binary.AsIndexed Alphabet as Idx⊕
open import Parser Alphabet
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
  uo ] = startsWith ]
  uo + = startsWith +

  data UnexpectedClosing : Type where
    EOF [ + aNum : UnexpectedClosing

  uc : UnexpectedClosing → Grammar _
  uc EOF = ε
  uc [ = startsWith [
  uc + = startsWith +
  uc aNum = anyNum ⊗ string

  data UnexpectedAdding : Type where
    [ ] aNum : UnexpectedAdding

  ua : UnexpectedAdding → Grammar _
  ua [ = startsWith [
  ua ] = startsWith ]
  ua aNum = anyNum ⊗ string

  Tok→State : Maybe Tok → AutomatonState
  Tok→State (just ]) = Closing
  Tok→State nothing = Adding
  Tok→State (just [) = Adding
  Tok→State (just +) = Adding
  Tok→State (just (num x)) = Adding

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

  DoneOpeningFun : ℕ → Maybe Tok → Functor (ℕ × AutomatonState)
  DoneOpeningFun n tok? = Var (n , Tok→State tok?) &e2 k (PeekChar tok?)

  DoneOpening : ℕ → Functor (ℕ × AutomatonState)
  DoneOpening n = ⊕e (Maybe Tok) (DoneOpeningFun n)

  AutomatonTy : Bool → ℕ × AutomatonState → Functor (ℕ × AutomatonState)
  AutomatonTy b (n , Opening) =
    ⊕e (AutomatonTag b n Opening)
      λ where
        left → k ＂ [ ＂ ⊗e Var (suc n , Opening)
        num → k anyNum ⊗e DoneOpening n
        (unexpectedO Eq.refl c) → k (uo c)
  AutomatonTy b (n , Closing) =
    ⊕e (AutomatonTag b n Closing)
      λ where
        (closeGood n-1 Eq.refl) → k ＂ ] ＂ ⊗e DoneOpening n-1
        (closeBad Eq.refl Eq.refl) → k (＂ ] ＂ ⊗ string)
        (unexpectedC Eq.refl c) → k (uc c)
  AutomatonTy b (n , Adding) =
    ⊕e (AutomatonTag b n Adding)
      λ where
        (doneGood Eq.refl Eq.refl) → k ε
        (doneBad n-1 Eq.refl Eq.refl) → k ε
        add → k ＂ + ＂ ⊗e Var (n , Opening)
        (unexpectedA Eq.refl c) → k (ua c)

  Trace : Bool → ℕ × AutomatonState → Grammar ℓ-zero
  Trace b = μ (AutomatonTy b)

  DoneOpeningG : Bool → ℕ → Grammar ℓ-zero
  DoneOpeningG b n = ⟦ DoneOpening n ⟧ (Trace b)

  -- After peeking, we choose a subsequent Guard and
  -- AutomatonState to transition to
  -- Here we ensure that the chosen guard and state match
  -- the ones prescribed by DoneOpening
  mkGuardPfs' : (n : ℕ) →
    Peek (&[ nq ∈ ℕ × AutomatonState ] ⊕[ b ∈ Bool ] Trace b nq)
    ⊢
    ⊕[ b ∈ Bool ] ⊕[ tok? ∈ Maybe Tok ] ⟦ DoneOpeningFun n tok? ⟧ (Trace b)
  mkGuardPfs' n =
    ⊕ᴰ-elim (λ tok? →
      map⊕ᴰ (λ b → σ tok? ∘g liftG ,&p liftG)
      ∘g &⊕ᴰ-distL≅ .fun
      ∘g π (n , Tok→State tok?) ,&p id)

  -- Whenever we want to use a Guard, this cuts out
  -- the redundant work in checking the guardedness condition
  mkGuardPfs : (n : ℕ) →
    &[ nq ∈ ℕ × AutomatonState ] ⊕[ b ∈ Bool ] Trace b nq
    ⊢
    ⊕[ b ∈ Bool ] ⊕[ tok? ∈ Maybe Tok ] ⟦ DoneOpeningFun n tok? ⟧ (Trace b)
  mkGuardPfs n = mkGuardPfs' n ∘g peek .fun

  parse : string ⊢
    &[ nq ∈ ℕ × AutomatonState ]
    ⊕[ b ∈ Bool ]
    Trace b nq
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
        ] → σ false ∘g roll ∘g σ (unexpectedO Eq.refl ]) ∘g liftG ∘g id ,⊗ string-intro
        + → σ false ∘g roll ∘g σ (unexpectedO Eq.refl +) ∘g liftG ∘g id ,⊗ string-intro
        (num x) → map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
                  ∘g ⊕ᴰ-distR .fun
                  ∘g σ x ,⊗ mkGuardPfs n
      (zero , Closing) →
        ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ string-intro
        ] → σ false ∘g roll ∘g σ (closeBad Eq.refl Eq.refl) ∘g liftG ∘g id ,⊗ string-intro
        + → σ false ∘g roll ∘g σ (unexpectedC Eq.refl UnexpectedClosing.+)
            ∘g liftG ∘g id ,⊗ string-intro
        (num x) → σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum) ∘g liftG ∘g σ x  ,⊗ string-intro
      (suc n-1 , Closing) →
        ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedC Eq.refl [) ∘g liftG ∘g id ,⊗ string-intro
        ] → map⊕ᴰ (λ _ → roll ∘g σ (closeGood n-1 Eq.refl) ∘g liftG ,⊗ id)
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ mkGuardPfs n-1
        + → σ false ∘g roll ∘g σ (unexpectedC Eq.refl UnexpectedClosing.+)
            ∘g liftG ∘g id ,⊗ string-intro
        (num x) → σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum) ∘g liftG ∘g σ x ,⊗ string-intro
      (n , Adding) → ⊕ᴰ-elim λ where
        [ → σ false ∘g roll ∘g σ (unexpectedA Eq.refl [) ∘g liftG ∘g id ,⊗ string-intro
        ] → σ false ∘g roll ∘g σ (unexpectedA Eq.refl ]) ∘g liftG ∘g id ,⊗ string-intro
        + → map⊕ᴰ (λ _ → roll ∘g σ add ∘g liftG ,⊗ liftG)
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ π (n , Opening)
        (num x) → σ false ∘g roll ∘g σ (unexpectedA Eq.refl aNum) ∘g liftG ∘g σ x ,⊗ string-intro)
      ∘g ⊕ᴰ-distL .fun
      )

  printAlg : (b : Bool) →
    Algebra (AutomatonTy b) (λ _ → string)
  printAlg b (n , Opening) =
    ⊕ᴰ-elim λ where
      left → CONS ∘g literal→char [ ,⊗ id ∘g lowerG ,⊗ lowerG
      num → CONS ∘g (⊕ᴰ-elim (literal→char ∘ num) ∘g lowerG) ,⊗ ⊕ᴰ-elim (λ _ → lowerG ∘g π₁)
      (unexpectedO Eq.refl EOF) → NIL ∘g lowerG
      (unexpectedO Eq.refl ]) → CONS ∘g literal→char ] ,⊗ id ∘g lowerG
      (unexpectedO Eq.refl +) → CONS ∘g literal→char Tok.+ ,⊗ id ∘g lowerG
  printAlg b (n , Closing) =
    ⊕ᴰ-elim λ where
      (closeGood n-1 Eq.refl) → CONS ∘g ((literal→char ] ∘g lowerG) ,⊗ ⊕ᴰ-elim (λ _ → lowerG ∘g π₁))
      (closeBad Eq.refl Eq.refl) → CONS ∘g literal→char ] ,⊗ id ∘g lowerG
      (unexpectedC Eq.refl EOF) → NIL ∘g lowerG
      (unexpectedC Eq.refl [) → CONS ∘g literal→char [ ,⊗ id ∘g lowerG
      (unexpectedC Eq.refl +) → CONS ∘g literal→char Tok.+ ,⊗ id ∘g lowerG
      (unexpectedC Eq.refl aNum) → CONS ∘g ⊕ᴰ-elim (literal→char ∘ num) ,⊗ id ∘g lowerG
  printAlg b (n , Adding) =
    ⊕ᴰ-elim λ where
      (doneGood Eq.refl Eq.refl) → NIL ∘g lowerG
      (doneBad n-1 Eq.refl Eq.refl) → NIL ∘g lowerG
      add → CONS ∘g literal→char Tok.+ ,⊗ id ∘g lowerG ,⊗ lowerG
      (unexpectedA Eq.refl [) → CONS ∘g literal→char [ ,⊗ id ∘g lowerG
      (unexpectedA Eq.refl ]) → CONS ∘g literal→char ] ,⊗ id ∘g lowerG
      (unexpectedA Eq.refl aNum) → CONS ∘g ⊕ᴰ-elim (literal→char ∘ num) ,⊗ id ∘g lowerG

  print : (b : Bool) → (ns : ℕ × AutomatonState) →
    Trace b ns ⊢ string
  print b = rec (AutomatonTy b) (printAlg b)

  Trace≅string : (nq : ℕ × AutomatonState) → ⊕[ b ∈ Bool ] Trace b nq ≅ string
  Trace≅string (n , s) .fun = ⊕ᴰ-elim (λ b → print b (n , s))
  Trace≅string (n , s) .inv = π (n , s) ∘g parse
  Trace≅string (n , s) .sec = unambiguous-string _ _
  Trace≅string (n , s) .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro π₁ ⇒-app
      {--
      -- For speed of typechecking it is crucial to separate the equality
      -- proofs into lemmas.
      --
      -- It is also important to scaffold typechecking
      -- by limiting inference for the signatures of these lemmas
      --}

      {--
      -- Convenient definitions to use in the type signatures of the equality lemmas
      --}
      module _ where
        goal : ℕ → AutomatonState → Grammar ℓ-zero
        goal n s = ⊕[ b ∈ Bool ] Trace b (n , s)

        l : (b : Bool) → (n : ℕ) → (s : AutomatonState) → Trace b (n , s) ⊢ goal n s
        l b n s = π (n , s) ∘g parse ∘g print b (n , s)

        r : (b : Bool) → (n : ℕ) → (s : AutomatonState) → Trace b (n , s) ⊢ goal n s
        r b n s = σ b

        the-eq : Bool → ℕ × AutomatonState → Grammar ℓ-zero
        the-eq b (n , s) = equalizer (l b n s) (r b n s)

        the-eq-π : (b : Bool) → ((n , s) : ℕ × AutomatonState) →
          equalizer (l b n s) (r b n s) ⊢ Trace b (n , s)
        the-eq-π b (n , s) = eq-π (l b n s) (r b n s)

        the-eq-π-pf : (b : Bool) → ((n , s) : ℕ × AutomatonState) →
          l b n s ∘g the-eq-π b (n , s) ≡ r b n s ∘g the-eq-π b (n , s)
        the-eq-π-pf b (n , s) = eq-π-pf (l b n s) (r b n s)

        L : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
          ⟦ AutomatonTy b (n , s) ⟧ (the-eq b) ⊢ goal n s
        L b n s = l b n s ∘g roll ∘g map (AutomatonTy b (n , s)) (the-eq-π b)

        R : (b : Bool) → (n : ℕ) → (s : AutomatonState) →
          ⟦ AutomatonTy b (n , s) ⟧ (the-eq b) ⊢ goal n s
        R b n s = r b n s ∘g roll ∘g map (AutomatonTy b (n , s)) (the-eq-π b)

        the-≡-ty : (b : Bool) → (n : ℕ) → (s : AutomatonState) → Type ℓ-zero
        the-≡-ty b n s = L b n s ≡ R b n s

        mk≡Ty : {A : Grammar ℓ-zero} →
          (b : Bool) → (n : ℕ) → (s : AutomatonState) →
          A ⊢ ⟦ AutomatonTy b (n , s) ⟧ (the-eq b) → Type ℓ-zero
        mk≡Ty b n s f = L b n s ∘g f ≡ R b n s ∘g f

      Opening≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Opening
      Opening≡ b n =
        ⊕ᴰ≡ _ _ λ where
        left → the-left-pf
        num → the-num-pf
        (unexpectedO Eq.refl c) → the-unexpected-pf c
          where
          the-left-pf : mk≡Ty b n Opening (σ left)
          the-left-pf i =
            map⊕ᴰ (λ b → roll ∘g σ left ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ eq-π-pf (l b (suc n) Opening) (r b (suc n) Opening) i ∘g lowerG ,⊗ lowerG

          the-num-pf' : (tok? : Maybe Tok) → (m : ℕ) →
            mk≡Ty b n Opening (σ num ∘g (liftG ∘g σ m) ,⊗ σ tok?)
          the-num-pf' tok? m =
            π (n , Opening) ∘g parse ∘g print b (n , Opening)
            ∘g roll ∘g σ num ∘g (liftG ∘g σ m) ,⊗ σ tok?
            ∘g id ,⊗ ((liftG ∘g the-eq-π b (n , Tok→State tok?) ∘g lowerG) ,&p id)
              ≡⟨ (λ i →
                    map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
                    ∘g ⊕ᴰ-distR .fun ∘g σ m ,⊗ id ∘g id ,⊗ mkGuardPfs' n
                    ∘g id ,⊗ remember tok? (~ i)
                    ∘g id ,⊗ ((parse ∘g print b (n , Tok→State tok?)
                               ∘g the-eq-π b (n , Tok→State tok?) ∘g lowerG) ,&p lowerG)
                  ) ⟩
            map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
            ∘g ⊕ᴰ-distR .fun ∘g σ m ,⊗ id ∘g id ,⊗ mkGuardPfs' n
            ∘g id ,⊗ σ tok?
            ∘g id ,⊗ ((parse ∘g print b (n , Tok→State tok?)
                       ∘g the-eq-π b (n , Tok→State tok?) ∘g lowerG) ,&p lowerG)
              ≡⟨ refl ⟩
            map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
            ∘g ⊕ᴰ-distR .fun ∘g σ m ,⊗ id ∘g id ,⊗ (map⊕ᴰ (λ _ → σ tok? ∘g liftG ,&p liftG))
            ∘g id ,⊗ &⊕ᴰ-distL≅ .fun
            ∘g id ,⊗ ((π (n , Tok→State tok?) ∘g parse ∘g print b (n , Tok→State tok?)
                      ∘g the-eq-π b (n , Tok→State tok?) ∘g lowerG) ,&p lowerG)
              ≡⟨ (λ i →
                   map⊕ᴰ (λ _ → roll ∘g σ num ∘g liftG ,⊗ id)
                   ∘g ⊕ᴰ-distR .fun
                   ∘g σ m ,⊗ id
                   ∘g id ,⊗ (map⊕ᴰ (λ _ → σ tok? ∘g liftG ,&p liftG))
                   ∘g id ,⊗ &⊕ᴰ-distL≅ .fun
                   ∘g id ,⊗ ((the-eq-π-pf b (n , Tok→State tok?) i ∘g lowerG) ,&p lowerG)
                 )
              ⟩
            σ b
            ∘g roll ∘g σ num ∘g (liftG ∘g σ m) ,⊗ σ tok?
            ∘g id ,⊗ ((liftG ∘g the-eq-π b (n , Tok→State tok?) ∘g lowerG) ,&p id)
            ∎

          the-num-pf : mk≡Ty b n Opening (σ num)
          the-num-pf i =
            ⊕ᴰ-elim (λ m → ⊕ᴰ-elim (λ tok? → the-num-pf' tok? m i) ∘g ⊕ᴰ-distR .fun)
            ∘g ⊕ᴰ-distL .fun ∘g lowerG ,⊗ id

          the-unexpected]-pf : mk≡Ty false n Opening (σ (unexpectedO Eq.refl ]))
          the-unexpected]-pf i =
            σ false ∘g roll ∘g σ (unexpectedO Eq.refl ])
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
          the-unexpected+-pf : mk≡Ty false n Opening (σ (unexpectedO Eq.refl +))
          the-unexpected+-pf i =
            σ false ∘g roll ∘g σ (unexpectedO Eq.refl +)
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG

          the-unexpected-pf : (c : UnexpectedOpening) →
            mk≡Ty false n Opening (σ (unexpectedO Eq.refl c))
          the-unexpected-pf EOF = refl
          the-unexpected-pf ] = the-unexpected]-pf
          the-unexpected-pf + = the-unexpected+-pf

      unexpectedClosing≡ : (n : ℕ) → (c : UnexpectedClosing) →
        mk≡Ty false n Closing (σ (unexpectedC Eq.refl c))
      unexpectedClosing≡ n EOF = refl
      unexpectedClosing≡ zero [ i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl [)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      unexpectedClosing≡ (suc n) [ i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl [)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      unexpectedClosing≡ zero + i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl +)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      unexpectedClosing≡ (suc n) + i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl +)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      unexpectedClosing≡ zero aNum i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      unexpectedClosing≡ (suc n) aNum i =
        σ false ∘g roll ∘g σ (unexpectedC Eq.refl aNum)
        ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG

      Closing≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Closing
      Closing≡ b zero = ⊕ᴰ≡ _ _ λ where
        (closeBad Eq.refl Eq.refl) → the-close-bad-pf
        (unexpectedC Eq.refl c) → unexpectedClosing≡ zero c
          where
          the-close-bad-pf : mk≡Ty false 0 Closing (σ (closeBad Eq.refl Eq.refl))
          the-close-bad-pf i =
            σ false ∘g roll ∘g σ (closeBad Eq.refl Eq.refl)
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
      Closing≡ b (suc n) = ⊕ᴰ≡ _ _ λ where
        (closeGood n-1 Eq.refl) → the-close-good-pf n-1
        (unexpectedC Eq.refl c) → unexpectedClosing≡ (suc n) c
          where

          the-close-good-pf' : (n-1 : ℕ) → (tok? : Maybe Tok) →
            mk≡Ty b (suc n-1) Closing (σ (closeGood n-1 Eq.refl) ∘g id ,⊗ σ tok?)
          the-close-good-pf' n-1 tok? =
            π (suc n-1 , Closing)
            ∘g parse
            ∘g print b (suc n-1 , Closing)
            ∘g roll ∘g σ (closeGood n-1 Eq.refl)
            ∘g id ,⊗ σ tok?
            ∘g id ,⊗ ((liftG ∘g the-eq-π b (n-1 , Tok→State tok?) ∘g lowerG) ,&p id)
              ≡⟨ (λ i →
                    map⊕ᴰ (λ _ → roll ∘g σ (closeGood n-1 Eq.refl))
                    ∘g ⊕ᴰ-distR .fun
                    ∘g id ,⊗ mkGuardPfs' n-1
                    ∘g id ,⊗ remember tok? (~ i)
                    ∘g id ,⊗ ((parse ∘g print b (n-1 , Tok→State tok?)
                               ∘g the-eq-π b (n-1 , Tok→State tok?) ∘g lowerG) ,&p lowerG)
                  ) ⟩
            map⊕ᴰ (λ _ → roll ∘g σ (closeGood n-1 Eq.refl))
            ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ mkGuardPfs' n-1
            ∘g id ,⊗ σ tok?
            ∘g id ,⊗ ((parse ∘g print b (n-1 , Tok→State tok?)
                       ∘g the-eq-π b (n-1 , Tok→State tok?) ∘g lowerG) ,&p lowerG)
              ≡⟨ (λ i →
                   map⊕ᴰ (λ _ → roll ∘g σ (closeGood n-1 Eq.refl))
                   ∘g ⊕ᴰ-distR .fun
                   ∘g id ,⊗ (map⊕ᴰ (λ _ → σ tok? ∘g liftG ,&p liftG))
                   ∘g id ,⊗ &⊕ᴰ-distL≅ .fun
                   ∘g id ,⊗ ((the-eq-π-pf b (n-1 , Tok→State tok?) i ∘g lowerG) ,&p lowerG)
                 )
              ⟩
            σ b
            ∘g roll ∘g σ (closeGood n-1 Eq.refl)
            ∘g id ,⊗ σ tok?
            ∘g id ,⊗ ((liftG ∘g the-eq-π b (n-1 , Tok→State tok?) ∘g lowerG) ,&p id)
            ∎

          the-close-good-pf :
            (n-1 : ℕ) →
            mk≡Ty b (suc n-1) Closing (σ (closeGood n-1 Eq.refl))
          the-close-good-pf n-1 i =
            ⊕ᴰ-elim (λ tok? → the-close-good-pf' n-1 tok? i)
            ∘g ⊕ᴰ-distR .fun

      Adding≡ : (b : Bool) → (n : ℕ) → the-≡-ty b n Adding
      Adding≡ b n = ⊕ᴰ≡ _ _ λ where
        (doneGood Eq.refl Eq.refl) → refl
        (doneBad n-1 Eq.refl Eq.refl) → refl
        add → the-add-pf
        (unexpectedA Eq.refl c) → the-unexpected-pf c
          where
          the-add-pf : mk≡Ty b n Adding (σ add)
          the-add-pf i =
            map⊕ᴰ (λ _ → roll ∘g σ add ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun
            ∘g id ,⊗ eq-π-pf (l b n Opening) (r b n Opening) i ∘g lowerG ,⊗ lowerG

          the-unexpected-pf :
            (c : UnexpectedAdding) →
            mk≡Ty false n Adding (σ (unexpectedA Eq.refl c))
          the-unexpected-pf [ i =
            σ false ∘g roll ∘g σ (unexpectedA Eq.refl [)
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
          the-unexpected-pf ] i =
            σ false ∘g roll ∘g σ (unexpectedA Eq.refl ])
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG
          the-unexpected-pf aNum i =
            σ false ∘g roll ∘g σ (unexpectedA Eq.refl aNum)
            ∘g liftG ∘g id ,⊗ unambiguous-string string-intro id i ∘g  lowerG

      the-ret : π (n , s) ∘g parse ∘g ⊕ᴰ-elim (λ b → print b (n , s)) ≡ id
      the-ret = ⊕ᴰ≡ _ _ λ b →
        equalizer-ind
          (AutomatonTy b)
          (λ (n , s) → ⊕[ b ∈ Bool ] Trace b (n , s))
          (λ (n , s) → π (n , s) ∘g parse ∘g print b (n , s))
          (λ (n , s) → σ b)
          (λ where
            (n , Opening) → Opening≡ b n
            (n , Closing) → Closing≡ b n
            (n , Adding) → Adding≡ b n
          )
          (n , s)

  unambiguous-⊕Trace : ∀ (nq : ℕ × AutomatonState) → unambiguous (⊕[ b ∈ Bool ] Trace b nq)
  unambiguous-⊕Trace nq = unambiguous≅ (sym≅ (Trace≅string nq)) unambiguous-string

  unambiguous-Trace : ∀ b nq → unambiguous (Trace b nq)
  unambiguous-Trace b nq = Idx⊕.unambig-summands (unambiguous-⊕Trace nq) b

  disjointAccRej : ∀ nq → disjoint (Trace true nq) (Trace false nq)
  disjointAccRej nq = hasDisjointSummands⊕ᴰ (unambiguous-⊕Trace nq) true false true≢false

  open Parser

  TraceParser : ∀ nq → Parser (Trace true nq) (Trace false nq)
  TraceParser nq .disj = disjointAccRej nq
  TraceParser nq .fun = Ind⊕→⊕ (λ b → Trace b nq) ∘g π nq ∘g parse

-- Soundness : from every trace we can extract an LL⟨1⟩ parse
module Soundness where
  open LL⟨1⟩
  open Automaton

  Stk : ℕ → Grammar ℓ-zero
  Stk zero = ε
  Stk (suc n) = ＂ ] ＂ ⊗ (＂ + ＂ ⊗ ATOM) * ⊗ Stk n

  ⟦_⟧State : ℕ × AutomatonState → Grammar ℓ-zero
  ⟦ n , Opening ⟧State = EXP ⊗ Stk n
  ⟦ n , Closing ⟧State = Stk n
  ⟦ n , Adding ⟧State = (＂ + ＂ ⊗ ATOM) * ⊗ Stk n

  buildExpAlg : Algebra (AutomatonTy true) ⟦_⟧State
  buildExpAlg (n , Opening) =
    ⊕ᴰ-elim λ where
      left → ATOM*→EXP ,⊗ id ∘g ⊗-assoc ∘g ⊸3⊗ (⊸3-intro-ε PARENS) ∘g lowerG ,⊗ lowerG
      num →
        (⊕ᴰ-elim λ where
          nothing → (ATOM*→EXP ∘g NUM ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ (lowerG ∘g π₁)
          (just [) → ((ATOM*→EXP ∘g NUM ,⊗ id) ,⊗ id ∘g ⊗-assoc) ∘g id ,⊗ (lowerG ∘g π₁)
          (just ]) → (DONE ∘g NUM) ,⊗ (lowerG ∘g π₁)
          (just +) → ((ATOM*→EXP ∘g NUM ,⊗ id) ,⊗ id ∘g ⊗-assoc) ∘g id ,⊗ (lowerG ∘g π₁)
          (just (num x)) → ((ATOM*→EXP ∘g NUM ,⊗ id) ,⊗ id ∘g ⊗-assoc) ∘g id ,⊗ (lowerG ∘g π₁))
        ∘g ⊕ᴰ-distR .fun
        ∘g lowerG ,⊗ id
  buildExpAlg (n , Closing) =
    ⊕ᴰ-elim λ where
      (closeGood n-1 Eq.refl) →
        lowerG ,⊗ ⊕ᴰ-elim λ where
          nothing → lowerG ∘g π₁
          (just [) → lowerG ∘g π₁
          (just ]) → NIL ,⊗ id ∘g ⊗-unit-l⁻ ∘g lowerG ∘g π₁
          (just +) → lowerG ∘g π₁
          (just (num x)) → lowerG ∘g π₁
  buildExpAlg (n , Adding) =
    ⊕ᴰ-elim λ where
      (doneGood Eq.refl Eq.refl) → NIL ,⊗ id ∘g ⊗-unit-r⁻ ∘g lowerG
      add →
        ⊕-elim
          (*-singleton _ ,⊗ id ∘g ⊗-assoc)
          ((CONS ∘g ⊗-assoc) ,⊗ id ∘g ⊗-assoc)
        ∘g ⊗⊕-distL
        ∘g id ,⊗ (⊗⊕-distR ∘g unrollEXP ,⊗ id)
        ∘g lowerG ,⊗ lowerG

  buildExp : Trace true (0 , Opening) ⊢ EXP
  buildExp = ⊗-unit-r ∘g rec _ buildExpAlg (0 , Opening)

-- Completeness : every LL⟨1⟩ parse has a corresponding accepting trace
module Completeness where
  open LL⟨1⟩
  open Automaton

  ⟦_⟧Nonterminal : Nonterminal → Grammar ℓ-zero
  ⟦ Exp ⟧Nonterminal = &[ n ∈ ℕ ] (DoneOpeningG true n ⊸ Trace true (n , Opening))
  ⟦ Atom ⟧Nonterminal = &[ n ∈ ℕ ] (DoneOpeningG true n ⊸ Trace true (n , Opening))

  mkTraceAlg : Algebra BinOpTy ⟦_⟧Nonterminal
  mkTraceAlg Exp =
    ⊕ᴰ-elim λ where
      done → id ∘g lowerG
      add → &ᴰ-intro (λ n → ⊸-intro (
            ⊸-app
            ∘g π n ,⊗ (((σ (just +) ∘g liftG ,&p liftG)
                       ∘g ((roll ∘g σ add ∘g liftG ,⊗ liftG)
                       ∘g id ,⊗ (⊸-app ∘g π n ,⊗ id)) ,& (id ,⊗ string-intro)) ∘g ⊗-assoc⁻)
            ∘g ⊗-assoc⁻
            ∘g (lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id))
  mkTraceAlg Atom =
    ⊕ᴰ-elim λ where
      num → &ᴰ-intro (λ n → ⊸-intro (roll ∘g σ num))
      parens → &ᴰ-intro (λ n → ⊸-intro (
               roll ∘g σ left ∘g liftG ,⊗ liftG
               ∘g id ,⊗
                  ((⊸-app
                  ∘g id ,⊗ (σ (just ]) ∘g liftG ,&p liftG)
                  ∘g π (suc n) ,⊗
                      (roll ∘g σ (closeGood n Eq.refl) ∘g liftG ,⊗ id) ,& (id ,⊗ string-intro))
                  ∘g ⊗-assoc⁻)
               ∘g ⊗-assoc⁻
               ∘g (lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id))

  mkTrace : EXP ⊢ Trace true (0 , Opening)
  mkTrace =
    ⊸-app
    ∘g id ,⊗ (σ nothing ∘g (liftG ∘g roll ∘g σ (doneGood Eq.refl Eq.refl) ∘g liftG) ,& liftG)
    ∘g ⊗-unit-r⁻ ∘g π 0 ∘g rec _ mkTraceAlg Exp

open WeakEquivalence

AccTrace≈EXP : Automaton.Trace true (0 , Automaton.Opening) ≈ LL⟨1⟩.EXP
AccTrace≈EXP .fun = Soundness.buildExp
AccTrace≈EXP .inv = Completeness.mkTrace

EXPParser : Parser LL⟨1⟩.EXP (Automaton.Trace false (0 , Automaton.Opening))
EXPParser = ≈Parser (Automaton.TraceParser (0 , Automaton.Opening)) AccTrace≈EXP
