{-- A printer is a function from the type of parse trees of a given string
 -- to Agda's builtin string type.
 --
 -- This is used mostly for visualizing the
 -- output of an extracted parser
 --}
{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Printer.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List
open import Erased.Data.Nat.Base
open import Erased.Data.Vec.Base as Vec using (Vec) renaming (_∷_ to _∷V_ ; [] to []V) public
open import Erased.Lift.Base
import Erased.Data.Sum.Base as Sum

open import Grammar Alphabet isSetAlphabet
open import Term Alphabet isSetAlphabet

open import Agda.Builtin.String renaming (String to BString)

_++B_ = primStringAppend
infixl 25 _++B_

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

record Printer (A : Grammar ℓA) : Type ℓA where
  field
    printTy : BString
    printParse : {w : String} → A w → BString

open Printer public

mkPrint : (n : ℕ) → BString → Vec BString n → BString
mkPrint zero label args = label
mkPrint (suc zero) label arg = label ++B "(" ++B Vec.head arg ++B ")"
mkPrint (suc (suc n)) label args =
  label ++B "(" ++B Vec.foldr (λ u v → u ++B " , " ++B v) "" args ++B ")"

module PrintingUtils (printAlphabet : Alphabet → BString) where
  printString : String → BString
  printString = foldr (λ c → printAlphabet c ++B_) ""

  printLiteral : ∀ c → Printer ＂ c ＂
  printLiteral c .printTy = "＂" ++B printAlphabet c ++B "＂"
  printLiteral c .printParse _ = mkPrint 1 "literal" (printAlphabet c ∷V []V)

  print-string : Printer string
  print-string .printTy = "string"
  print-string .printParse {w = w} _ = printString w

  opaque
    unfolding _⊗_
    print⊗ : Printer A → Printer B → Printer (A ⊗ B)
    print⊗ printA printB .printTy = printA .printTy ++B " ⊗ " ++B printB .printTy
    print⊗ printA printB .printParse (s , a , b) = mkPrint 2 "⊗" (printA .printParse a ∷V printB .printParse b ∷V []V)

    {-# TERMINATING #-}
    print* : Printer A → Printer (A *)
    print* printA .printTy = mkPrint 1 "" ((printA .printTy) ∷V []V) ++B "*"
    print* printA .printParse (roll w' (nil , _)) = mkPrint 0 "nil" []V
    print* printA .printParse (roll w' (cons , (s , lift a , lift the-*))) =
      mkPrint 2 "cons" (printA .printParse a ∷V (print* printA .printParse the-*) ∷V []V)

  opaque
    unfolding _⊕_
    print⊕ : Printer A → Printer B → Printer (A ⊕ B)
    print⊕ printA printB .printTy = printA .printTy ++B "⊕" ++B printB .printTy
    print⊕ printA printB .printParse (Sum.inl a) = mkPrint 1 "inl" (printA .printParse a ∷V []V)
    print⊕ printA printB .printParse (Sum.inr b) = mkPrint 1 "inr" (printB .printParse b ∷V []V)

  print⊢ : Printer A → Printer B → A ⊢ B → (w : String) → A w → BString
  print⊢ printA printB e w a =
    "input string: " ++B printString w ++B "\n" ++B
    -- "input parse of " ++B printA .printTy ++B " : " ++B printA .printParse a ++B "\n" ++B
    "output parse of " ++B printB .printTy ++B " : " ++B printB .printParse (e w a)

  -- For now, implicitly ignore all of the lifts
  -- They are annoying to deal with, and arise a lot when dealing with inductives
  printLift : {ℓ : Level} → Printer A → Printer (LiftG ℓ A)
  printLift printA .printTy = printA .printTy
  printLift printA .printParse (lift a) = printA .printParse a
