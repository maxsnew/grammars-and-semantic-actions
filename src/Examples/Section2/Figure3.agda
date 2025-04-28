{-# OPTIONS --erased-cubical #-}
module Examples.Section2.Figure3 where

open import Cubical.Foundations.Prelude hiding (lower ; lift ; Lift)
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Erased.Lift.Base
import Erased.Data.Equality.Base as Eq
import Erased.Data.Sum.Base as Sum

open import Examples.Section2.Alphabet
open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Inductive.AsEquality.Indexed Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.String.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet


open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
import Agda.Builtin.String as BuiltinString

postulate putStrLn : BuiltinString.String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

_++B_ = BuiltinString.primStringAppend
infixl 25 _++B_

A B : Grammar ℓ-zero
A = ＂ a ＂ ⊗ ＂ b ＂
B = (＂ a ＂ *) ⊗ ＂ b ＂ ⊕ ＂ c ＂

private
  variable
    ℓC ℓD : Level
    C : Grammar ℓC
    D : Grammar ℓD
    w : String

printer : Grammar ℓC → Type ℓC
printer C = ∀ (w : String) → C w → BuiltinString.String

printAlphabet : Alphabet → BuiltinString.String
printAlphabet a = "a"
printAlphabet b = "b"
printAlphabet c = "c"

printStringHelp : String → BuiltinString.String
printStringHelp [] = ""
printStringHelp (character ∷ []) = printAlphabet character
printStringHelp (character ∷ w) = printAlphabet character ++B printStringHelp w

printString : String → BuiltinString.String
printString w = "＂" ++B printStringHelp w ++B "＂"

printLiteral : ∀ character → printer ＂ character ＂
printLiteral character lit w = "literal(" ++B printAlphabet character ++B ")"

opaque
  unfolding _⊗_ _⊕_
  print⊗ : printer C → printer D → printer (C ⊗ D)
  print⊗ printC printD w (s , the-c , the-d) =
    "[ " ++B printString (leftEq s) ++B " - " ++B printC _ the-c ++B " ] ⊗ [ "
        ++B printString (rightEq s) ++B " - " ++B printD _ the-d ++B " ]"

  {-# TERMINATING #-}
  print* : printer C → printer (C *)
  print* printC w (roll w' (nil , v)) = "NIL"
  print* printC w (roll w' (cons , (s , the-c , the-*))) = "CONS " ++B print⊗ printC (print* printC) _ (s , lower the-c , lower the-*)

  print⊕ : printer C → printer D → printer (C ⊕ D)
  print⊕ printC printD w (Sum.inl the-c) = "INL " ++B printC w the-c
  print⊕ printC printD w (Sum.inr the-d) = "INR " ++B printD w the-d

  printA : printer A
  printA = print⊗ (printLiteral a) (printLiteral b)

  printB : printer B
  printB = print⊕ (print⊗ (print* (printLiteral a)) (printLiteral b)) (printLiteral c)

print⊢ : printer C → printer D → C ⊢ D → (w : String) → C w → BuiltinString.String
print⊢ printC printD e w the-c = "IN: " ++B printC w the-c ++B "\nOUT: " ++B printD w (e w the-c)

testString : String
testString = a ∷ b ∷ []

opaque
  unfolding _⊗_
  mkA : A testString
  mkA = (_ , Eq.refl) , lit-intro , lit-intro

g : A ⊢ B
g = inl ∘g (CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id

h : string ⊢ B
h = ?

main : IO ⊤
main = putStrLn (print⊢ printA printB g testString mkA)
