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

Num = Digit *

open Printer
open PrintingUtils primShowChar

printDigit : Printer Digit
printDigit =
  print⊕ᴰ "Digit'"
    (λ d → primShowChar (Digit'→BChar d))
    (λ dString → join ("⟦ " ∷ dString ∷ " ⟧Digit" ∷ []))
    (λ d → printLiteral (Digit'→BChar d))

printNum : Printer Num
printNum = print* printDigit

unicodeChar→Num? : char ⊢ Maybe Num
unicodeChar→Num? = ⊕ᴰ-elim λ c →
  foldr
    (λ d acc →
      decRec
        (λ where Eq.refl → just ∘g *-singleton Digit ∘g σ d)
        (λ _ → acc)
        (charDecEq c (Digit'→BChar d))
    )
    nothing
    Digit'List

concatNum : Num ⊗ Num ⊢ Num
concatNum = flatten*

open StrongEquivalence

ℕParser : WeakParser Num
ℕParser = fold*r char
  (inl ∘g NIL)
  (fmap concatNum
  ∘g Maybe⊗
  ∘g unicodeChar→Num? ,⊗ id)


main : Main
main = run (do
  putStrLn "Please enter a number"
  n ← getLine
  putStr "Got input: "
  putStr (printString (primStringToList n))
  putStrLn "\n"
  putStrLn (printParser (printMaybe printNum) ℕParser (primStringToList n))
  )
