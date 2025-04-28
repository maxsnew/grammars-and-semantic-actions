{-# OPTIONS --erased-cubical --guardedness #-}
module Examples.Section2.Figure3 where

open import Cubical.Foundations.Prelude hiding (lower ; lift ; Lift)
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Erased.Lift.Base
import Erased.Data.Equality.Base as Eq
import Erased.Data.Sum.Base as Sum
open import Erased.Relation.Nullary.Base

open import Examples.Section2.Alphabet
open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Inductive.AsEquality.Indexed Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Sum Alphabet isSetAlphabet
open import Grammar.String.Base Alphabet isSetAlphabet
open import Grammar.String.Properties Alphabet isSetAlphabet
import Grammar.Top.Base Alphabet isSetAlphabet as ⊤G
open import Term.Base Alphabet isSetAlphabet


open import IO
import Agda.Builtin.String as BuiltinString

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

print-string : printer string
print-string w _ = printString w

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

open StrongEquivalence

-- Unclear how to get decidable equality type for an arbitrary FinSet
-- without going through Data.Equality.Conversion (which cannot be used at runtime)
decEqAlphabet : DecEq Alphabet
decEqAlphabet a a = yes Eq.refl
decEqAlphabet b b = yes Eq.refl
decEqAlphabet c c = yes Eq.refl
decEqAlphabet a b = no (λ ())
decEqAlphabet a c = no (λ ())
decEqAlphabet b a = no (λ ())
decEqAlphabet b c = no (λ ())
decEqAlphabet c a = no (λ ())
decEqAlphabet c b = no (λ ())

literalParser : (character : Alphabet) → string ⊢ ＂ character ＂ ⊕ string
literalParser character =
  fold*r char
    (inr ∘g string-intro)
    (⊕ᴰ-elim (λ character' →
      ⊕-elim
        (inr ∘g string-intro)
        (⊕-elim
          (decRec
            (λ where Eq.refl → inl)
            (λ _ → inr ∘g string-intro)
            (decEqAlphabet character character')
          ∘g ⊗-unit-r)
          (inr ∘g string-intro)
        ∘g ⊗⊕-distL
        ∘g id ,⊗ unroll-string≅ .fun)
      ∘g ⊗⊕-distL)
     ∘g ⊕ᴰ-distLEq .fun)

h : string ⊢ A ⊕ string
h = fold*r char
  (inr ∘g string-intro)
  (⊕-elim
    (inr ∘g string-intro)
    (⊕-elim
      (⊕-elim
        inl
        (inr ∘g string-intro)
      ∘g ⊗⊕-distR)
      (inr ∘g string-intro)
    ∘g ⊗⊕-distL)
  ∘g ⊗⊕-distL
  ∘g (literalParser a ∘g string-intro) ,⊗ (id ,⊕p literalParser b))

printA⊕string : printer (A ⊕ string)
printA⊕string = print⊕ printA print-string

s' : String
s' = a ∷ b ∷ c ∷ a ∷ []

main : Main
main = run (do
  putStrLn "\n\n"
  putStrLn (print⊢ printA printB g testString mkA)
  putStrLn "\n\n"
  putStrLn (print⊢ print-string printA⊕string h testString (mkstring testString))
  putStrLn "\n\n"
  putStrLn (print⊢ print-string printA⊕string h s' (mkstring s'))
  )
