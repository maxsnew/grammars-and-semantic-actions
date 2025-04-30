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
open import Erased.Lift.Base
import Erased.Data.Sum.Base as Sum

open import Grammar Alphabet isSetAlphabet
open import Grammar.Maybe Alphabet isSetAlphabet
open import Term Alphabet isSetAlphabet

open import Agda.Builtin.String renaming (String to BString)

_++B_ = primStringAppend
infixl 25 _++B_

join : List BString → BString
join = foldr _++B_ ""

joinDelimited : BString → List BString → BString
joinDelimited delimiter [] = ""
joinDelimited delimiter (s ∷ []) = s
joinDelimited delimiter (s ∷ s' ∷ strings) = foldr (λ s s' → s ++B delimiter ++B s') "" (s ∷ s' ∷ strings)

private
  variable
    ℓA ℓB ℓX : Level
    X : Type ℓX
    A : Grammar ℓA
    B : Grammar ℓB

record Printer (A : Grammar ℓA) : Type ℓA where
  field
    printTy : BString
    printParse : {w : String} → A w → BString

open Printer public

mkPrint : BString → List BString → BString
mkPrint label args = label ++B mkArgs args
  where
  mkArgs : List BString → BString
  mkArgs [] = ""
  mkArgs (s ∷ strings) = join ("(" ∷ joinDelimited " , " args ∷ ")" ∷ [])

module PrintingUtils (printAlphabet : Alphabet → BString) where
  printString : String → BString
  printString = foldr (λ c → printAlphabet c ++B_) ""

  printLiteral : ∀ c → Printer ＂ c ＂
  printLiteral c .printTy = join ("＂" ∷ printAlphabet c ∷ "＂" ∷ [])
  printLiteral c .printParse _ = mkPrint "literal" (printAlphabet c ∷ [])

  print-string : Printer string
  print-string .printTy = "string"
  print-string .printParse {w = w} _ = printString w

  opaque
    unfolding _⊗_
    print⊗ : Printer A → Printer B → Printer (A ⊗ B)
    print⊗ printA printB .printTy = join (printA .printTy ∷ " ⊗ " ∷ printB .printTy ∷ [])
    print⊗ printA printB .printParse (s , a , b) = mkPrint "⊗" (printA .printParse a ∷ printB .printParse b ∷ [])

    {-# TERMINATING #-}
    print* : Printer A → Printer (A *)
    print* printA .printTy = mkPrint "" ((printA .printTy) ∷ []) ++B "*"
    print* printA .printParse (roll w' (nil , _)) = mkPrint "nil" []
    print* printA .printParse (roll w' (cons , (s , lift a , lift the-*))) =
      mkPrint "cons" (printA .printParse a ∷ (print* printA .printParse the-*) ∷ [])

  opaque
    unfolding _⊕_
    print⊕ : Printer A → Printer B → Printer (A ⊕ B)
    print⊕ printA printB .printTy = join (printA .printTy ∷ " ⊕ " ∷ printB .printTy ∷ [])
    print⊕ printA printB .printParse (Sum.inl a) = mkPrint "inl" (printA .printParse a ∷ [])
    print⊕ printA printB .printParse (Sum.inr b) = mkPrint "inr" (printB .printParse b ∷ [])

  opaque
    unfolding _&_
    print& : Printer A → Printer B → Printer (A & B)
    print& printA printB .printTy = join (printA .printTy ∷ " & " ∷ printB .printTy ∷ [])
    print& printA printB .printParse (a , b) = mkPrint "&" (printA .printParse a ∷ printB .printParse b ∷ [])

  module _ {A : X → Grammar ℓA}
    (printXTy : BString)
    (printX : X → BString)
    (printIdxATy : BString → BString)
    (printA : (x : X) → Printer (A x)) where
    print⊕ᴰ : Printer (⊕[ x ∈ X ] A x)
    print⊕ᴰ .printTy = join ("⊕[ x ∈ " ∷ printXTy ∷ " ] " ∷ printIdxATy "x" ∷ [])
    print⊕ᴰ .printParse (x , a) = mkPrint "σ" (printX x ∷ printA x .printParse a ∷ [])

  module _ {A : X → Grammar ℓA}
    (printXTy : BString)
    (printIdxATy : BString → BString) where
    print&ᴰ : Printer (&[ x ∈ X ] A x)
    print&ᴰ .printTy = join ("&[ x ∈ " ∷ printXTy ∷ " ] " ∷ printIdxATy "x" ∷ [])
    print&ᴰ .printParse f = mkPrint (join ("∀(x : " ∷ printXTy ∷ ")" ∷ [])) (printIdxATy "x" ∷ [])

  print⊤ : Printer ⊤
  print⊤ .printTy = "⊤"
  print⊤ .printParse _ = mkPrint "tt" []

  printMaybe : Printer A → Printer (Maybe A)
  printMaybe printA = print⊕ printA print⊤

  print⊢ : Printer A → Printer B → A ⊢ B → (w : String) → A w → BString
  print⊢ printA printB e w a =
    "input string: " ++B printString w ++B "\n" ++B
    "input parse of " ++B printA .printTy ++B " : " ++B printA .printParse a ++B "\n" ++B
    "output parse of " ++B printB .printTy ++B " : " ++B printB .printParse (e w a)

  printParser : Printer A → string ⊢ A → (w : String) → BString
  printParser printA e w =
    "input string: " ++B printString w ++B "\n" ++B
    "output parse of " ++B printA .printTy ++B " : " ++B printA .printParse (e w (mkstring w))

  -- For now, implicitly ignore all of the lifts
  -- They are annoying to deal with, and arise a lot when dealing with inductives
  printLift : {ℓ : Level} → Printer A → Printer (LiftG ℓ A)
  printLift printA .printTy = printA .printTy
  printLift printA .printParse (lift a) = printA .printParse a
