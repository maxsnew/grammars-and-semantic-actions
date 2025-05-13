{-# OPTIONS --erased-cubical --guardedness #-}
module Examples.Unicode.Nat where

open import Cubical.Foundations.Prelude hiding (lower ; lift ; Lift)
open import Erased.Data.Nat.Base
open import Erased.Data.List

open import Erased.Lift.Base
import Erased.Data.Equality.Base as Eq
import Erased.Data.Sum.Base as Sum
open import Erased.Data.Bool.Base hiding (_⊕_)
open import Erased.Data.Bool.SwitchStatement
import Erased.Data.Maybe.Base as Maybe
open import Erased.Relation.Nullary.Base

open import String.Unicode

open import Grammar UnicodeChar isSetUnicodeChar
open import Grammar.Maybe UnicodeChar isSetUnicodeChar
open import Term UnicodeChar isSetUnicodeChar
open import Parser UnicodeChar isSetUnicodeChar
open import Printer.Base UnicodeChar isSetUnicodeChar

open import IO
open import Agda.Builtin.String renaming (String to BString)
open import Agda.Builtin.Char renaming (Char to BChar)
open import Data.String.Properties using (_==_)

data Digit' : Type ℓ-zero where
  zero' one' two' three' four' five' six' seven' eight' nine' : Digit'

Digit'List : List Digit'
Digit'List = zero' ∷ one' ∷ two' ∷ three' ∷ four' ∷ five' ∷ six' ∷ seven' ∷ eight' ∷ nine' ∷ []

Digit'→BChar : Digit' → BChar
Digit'→BChar zero' = '0'
Digit'→BChar one' = '1'
Digit'→BChar two' = '2'
Digit'→BChar three' = '3'
Digit'→BChar four' = '4'
Digit'→BChar five' = '5'
Digit'→BChar six' = '6'
Digit'→BChar seven' = '7'
Digit'→BChar eight' = '8'
Digit'→BChar nine' = '9'

⟦_⟧Digit : Digit' → Grammar ℓ-zero
⟦ d ⟧Digit = ＂ Digit'→BChar d ＂

Digit : Grammar ℓ-zero
Digit = ⊕[ d ∈ Digit' ] ⟦ d ⟧Digit

Num = Digit +

open Printer
open PrintingUtils (λ c → primStringFromList (c ∷ []))

printDigit : Printer Digit
printDigit =
  print⊕ᴰ "Digit'"
    (λ d → primShowChar (Digit'→BChar d))
    (λ dString → join ("⟦ " ∷ dString ∷ " ⟧Digit" ∷ []))
    (λ d → printLiteral (Digit'→BChar d))

printNum : Printer Num
printNum = print⊗ printDigit (print* printDigit)

unicodeChar→Num? : char ⊢ Maybe Num
unicodeChar→Num? = ⊕ᴰ-elim λ c →
  foldr
    (λ d acc →
      decRec
        (λ where Eq.refl → just ∘g +-singleton Digit ∘g σ d)
        (λ _ → acc)
        (charDecEq c (Digit'→BChar d))
    )
    nothing
    Digit'List

concatNum : Num ⊗ Num ⊢ Num
concatNum = id ,⊗ (flatten* ∘g id ,⊗ CONS) ∘g ⊗-assoc⁻

open StrongEquivalence

Digit*Parser : WeakParser (Digit *)
Digit*Parser =
  fold*r char
  (just ∘g NIL)
  (fmap (flatten* ∘g CONS ,⊗ id)
  ∘g Maybe⊗
  ∘g unicodeChar→Num? ,⊗ id)

ℕParser : WeakParser Num
ℕParser =
  ⊕-elim
    nothing
    (fmap (id ,⊗ flatten* ∘g ⊗-assoc⁻)
    ∘g Maybe⊗
    ∘g unicodeChar→Num? ,⊗ Digit*Parser)
  ∘g unroll-string≅ .fun

Digit'→ℕ : Digit' → ℕ
Digit'→ℕ zero' = 0
Digit'→ℕ one' = 1
Digit'→ℕ two' = 2
Digit'→ℕ three' = 3
Digit'→ℕ four' = 4
Digit'→ℕ five' = 5
Digit'→ℕ six' = 6
Digit'→ℕ seven' = 7
Digit'→ℕ eight' = 8
Digit'→ℕ nine' = 9

Digit*→ℕ' : Digit * ⊢ ⊕[ n ∈ ℕ ] ⊕[ depth ∈ ℕ ] ⊤
Digit*→ℕ' =
  fold*r Digit
    (σ 0 ∘g σ 0 ∘g ⊤-intro)
    (⊕ᴰ-elim (λ dig →
      ⊕ᴰ-elim (λ n →
        ⊕ᴰ-elim (λ depth →
          σ ((10 ^ depth) · Digit'→ℕ dig + n)
          ∘g σ (suc depth)
          ∘g ⊤-intro
        )
        ∘g ⊕ᴰ-distREq .fun
      )
      ∘g ⊕ᴰ-distREq .fun
    )
    ∘g ⊕ᴰ-distLEq .fun)

Num→ℕ' : Num ⊢ ⊕[ n ∈ ℕ ] ⊕[ depth ∈ ℕ ] ⊤
Num→ℕ' = Digit*→ℕ' ∘g +→* Digit

Num→ℕ : ∀ {w} → Num w → ℕ
Num→ℕ n = Num→ℕ' _ n .fst

readℕ : BString → Maybe.Maybe ℕ
readℕ s = Maybe.map-Maybe Num→ℕ (extractMaybe (runWeakParser ℕParser (primStringToList s)))

{-# TERMINATING #-}
repl : IO _
repl = do
  input ← getLine
  if input == "quit"
    then putStrLn "Goodbye!"
    else do
      putStrLn (printParser (printMaybe printNum) ℕParser (primStringToList input))
      repl

main : Main
main = run do
  putStrLn "Please enter a number"
  repl
