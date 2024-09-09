module Examples.Arith where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

data BinOp : Type where
  + * : BinOp

data Tok : Type where
  [ ] : Tok
  binOp : BinOp → Tok
  num : ℕ → Tok

Alphabet : hSet _
Alphabet = Tok , {!!}

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

module v0 where
  -- ambiguous grammar
  data Arith : Grammar ℓ-zero where
    num : ∀ {n} → literal (num n) ⊢ Arith
    parens : literal [ ⊗ Arith ⊗ literal ] ⊢ Arith
    binOp : ∀ {b} → Arith ⊗ literal (binOp b) ⊗ Arith ⊢ Arith


module v1 where
  -- add precedence, associativity. Should be *weakly* equivalent to
  -- previous

  data Sum : Grammar ℓ-zero
  data Prod : Grammar ℓ-zero
  data Atom : Grammar ℓ-zero

  data Sum where
    plus : Prod ⊗ literal (binOp +) ⊗ Sum ⊢ Sum
    arg  : Prod ⊢ Sum

  data Prod where
    times : Atom ⊗ literal (binOp *) ⊗ Prod ⊢ Prod
    arg : Atom ⊢ Prod

  data Atom where
    num : ∀ {n : ℕ} → literal (num n) ⊢ Atom
    parens : literal [ ⊗ Sum ⊗ literal ] ⊢ Atom

  Arith = Sum

  module _ {ℓS ℓP ℓA}
    {[S] : Grammar ℓS}
    {[P] : Grammar ℓP}
    {[A] : Grammar ℓA} where
    module _
      ([plus] : [P] ⊗ literal (binOp +) ⊗ [S] ⊢ [S])
      ([argS] : [P] ⊢ [S])
      ([times] : [A] ⊗ literal (binOp *) ⊗ [P] ⊢ [P])
      ([argP] : [A] ⊢ [P])
      ([num] : ∀ {n} → literal (num n) ⊢ [A])
      ([parens] : literal [ ⊗ [S] ⊗ literal ] ⊢ [A])
      where
      -- this TERMINATING is totally banal and can be avoided easily but meh
      {-# TERMINATING #-}
      recP : Prod ⊢ [P]
      recS : Sum ⊢ [S]
      recA : Atom ⊢ [A]
      recS w (plus .w x) =
        ([plus] ∘g ⊗-intro recP (⊗-intro id recS)) w x
      recS w (arg .w x) =
        ([argS] ∘g recP) w x
      recP w (times .w x) =
        ([times] ∘g ⊗-intro recA (⊗-intro id recP)) w x
      recP w (arg .w x) = ([argP] ∘g recA) w x
      recA w (num .w x) = [num] w x
      recA w (parens .w x) =
        ([parens] ∘g ⊗-intro id (⊗-intro recS id)) w x
-- -- add associativity, show weak equivalence
module v2 where
  -- make LL(1), should be *strongly* equivalent to previous
  Sum : Grammar ℓ-zero
  data Prod⊸Sum : Grammar ℓ-zero
  Prod : Grammar ℓ-zero
  data Atom⊸Prod : Grammar ℓ-zero
  data Atom : Grammar ℓ-zero

  Sum = Prod ⊗ Prod⊸Sum
  data Prod⊸Sum where
    plus : literal (binOp +) ⊗ Sum ⊢ Prod⊸Sum
    arg  : ε-grammar ⊢ Prod⊸Sum

  Prod = Atom ⊗ Atom⊸Prod

  data Atom⊸Prod where
    times : literal (binOp *) ⊗ Prod ⊢ Atom⊸Prod
    arg : ε-grammar ⊢ Atom⊸Prod

  data Atom where
    num : ∀ {n : ℕ} → literal (num n) ⊢ Atom
    parens : literal [ ⊗ Sum ⊗ literal ] ⊢ Atom

  Arith = Sum

  module _ {ℓS ℓPS ℓP ℓAP ℓA}
    {[S] : Grammar ℓS}
    {[PS] : Grammar ℓPS}
    {[P] : Grammar ℓP}
    {[AP] : Grammar ℓAP}
    {[A] : Grammar ℓA} where
    module _
      ([mkS] : [P] ⊗ [PS] ⊢ [S])
      ([plus] : literal (binOp +) ⊗ [S] ⊢ [PS])
      ([argPS] : ε-grammar ⊢ [PS])
      ([mkP] : [A] ⊗ [AP] ⊢ [P])
      ([times] : literal (binOp *) ⊗ [P] ⊢ [AP])
      ([argAP] : ε-grammar ⊢ [AP])
      ([num] : ∀ {n} → literal (num n) ⊢ [A])
      ([parens] : literal [ ⊗ [S] ⊗ literal ] ⊢ [A])
      where
      -- this TERMINATING block is totally benign
      {-# TERMINATING #-}
      recP : Prod ⊢ [P]
      recPS : Prod⊸Sum ⊢ [PS]
      recS : Sum ⊢ [S]
      recAP : Atom⊸Prod ⊢ [AP]
      recA : Atom ⊢ [A]
      recS = [mkS] ∘g ⊗-intro recP recPS
      recPS w (plus .w x) = [plus] w (⊗-intro id recS w x)
      recPS w (arg .w x) = [argPS] w x
      recP = [mkP] ∘g ⊗-intro recA recAP
      recAP w (times .w x) = [times] w (⊗-intro id recP w x)
      recAP w (arg .w x) = [argAP] w x
      recA w (num .w x) = [num] w x
      recA w (parens .w x) =
        ([parens] ∘g ⊗-intro id (⊗-intro recS id)) w x

ll1-correct : StrongEquivalence v1.Arith v2.Arith
ll1-correct = mkStrEq
  (v1.recS
    {[S] = v2.Sum}
    {[P] = v2.Prod}
    {[A] = v2.Atom}
    (⊗-intro id v2.plus)
    (⊗-intro id v2.arg ∘g ⊗-unit-r⁻)
    (⊗-intro id v2.times)
    (⊗-intro id v2.arg ∘g ⊗-unit-r⁻)
    v2.num
    v2.parens)
  (v2.recS
    {[S] = v1.Sum}
    {[PS] = v1.Prod ⊸ v1.Sum}
    {[P] = v1.Prod}
    {[AP] = v1.Atom ⊸ v1.Prod}
    {[A] = v1.Atom}
    ⊸-app
    (⊸-intro v1.plus)
    (⊸-intro {k = v1.Sum} (v1.arg ∘g ⊗-unit-r))
    ⊸-app
    (⊸-intro v1.times)
    (⊸-intro {k = v1.Prod} (v1.arg ∘g ⊗-unit-r))
    v1.num
    v1.parens)
  {!!}
  {!!}
