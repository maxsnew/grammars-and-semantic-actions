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

open import String.ASCII.Base

open import Grammar ASCIIChar isSetASCIIChar
open import Grammar.Maybe ASCIIChar isSetASCIIChar
open import Term ASCIIChar isSetASCIIChar
open import Parser ASCIIChar isSetASCIIChar
open import Printer.Base ASCIIChar isSetASCIIChar

open import IO
open import Agda.Builtin.String renaming (String to BString)
open import Agda.Builtin.Char renaming (Char to BChar)

data Digit' : Type ℓ-zero where
  zero' one' two' three' four' five' six' seven' eight' nine' : Digit'

Digit'List : List Digit'
Digit'List = zero' ∷ one' ∷ two' ∷ three' ∷ four' ∷ five' ∷ six' ∷ seven' ∷ eight' ∷ nine' ∷ []

Digit'→ASCIIChar : Digit' → ASCIIChar
Digit'→ASCIIChar zero' = zero^
Digit'→ASCIIChar one' = one^
Digit'→ASCIIChar two' = two^
Digit'→ASCIIChar three' = three^
Digit'→ASCIIChar four' = four^
Digit'→ASCIIChar five' = five^
Digit'→ASCIIChar six' = six^
Digit'→ASCIIChar seven' = seven^
Digit'→ASCIIChar eight' = eight^
Digit'→ASCIIChar nine' = nine^

⟦_⟧Digit : Digit' → Grammar ℓ-zero
⟦ d ⟧Digit = ＂ Digit'→ASCIIChar d ＂

Digit : Grammar ℓ-zero
Digit = ⊕[ d ∈ Digit' ] ⟦ d ⟧Digit

Num = Digit *


open Printer
open PrintingUtils ASCII→UnicodeString

printDigit : Printer Digit
printDigit =
  print⊕ᴰ "Digit'"
    (λ d → ASCII→UnicodeString (Digit'→ASCIIChar d))
    (λ dString → join ("⟦ " ∷ dString ∷ " ⟧Digit" ∷ []))
    (λ d → printLiteral (Digit'→ASCIIChar d))

printNum : Printer Num
printNum = print* printDigit

unicodeChar→Num? : char ⊢ Maybe Num
unicodeChar→Num? = ⊕ᴰ-elim λ c →
  decRec
    (λ where Eq.refl → just ∘g *-singleton Digit ∘g σ one')
    (λ _ → nothing)
    (decEqASCII c one^)
      -- decRec
      --   (λ where Eq.refl → just ∘g *-singleton Digit ∘g σ one')
      --   (λ _ → nothing)
      --   (charDecEq c (Digit'→ASCIIChar one'))
  -- foldr
  --   (λ d acc →
  --     decRec
  --       (λ where Eq.refl → just ∘g *-singleton Digit ∘g σ d)
  --       (λ _ → acc)
  --       (charDecEq c (Digit'→ASCIIChar d))
  --   )
  --   nothing
  --   Digit'List

concatNum : Num ⊗ Num ⊢ Num
concatNum = flatten*

open StrongEquivalence

ℕParser : WeakParser Num
ℕParser = fold*r char
  (inr ∘g ⊤-intro)
  (fmap concatNum
  ∘g Maybe⊗
  ∘g unicodeChar→Num? ,⊗ id)


main : Main
main = run (do
  putStrLn "Please enter a number"
  n ← getLine
  putStr "Got input: "
  putStr (primShowString n)
  putStrLn "\n"
  putStrLn (printParser (printMaybe printNum) ℕParser {!!})
  )
