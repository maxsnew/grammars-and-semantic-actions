{- Some presentations of the Dyck grammar of balanced parentheses and hopefully some parsers? -}

module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_ ;_or_)
open import Cubical.Data.List hiding (init)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

data Bracket : Type where
  [ ] : Bracket

BracketRep : Bracket ≃ Bool
BracketRep = isoToEquiv (iso
  (λ { [ → true ; ] → false })
  (λ { false → ] ; true → [ })
  (λ { false → refl ; true → refl })
  λ { [ → refl ; ] → refl })

isFinBracket : isFinSet Bracket
isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

Alphabet : hSet _
Alphabet = (Bracket , isFinSet→isSet isFinBracket)

open import Grammar Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Term Alphabet
open import String.More Alphabet
open import Parser Alphabet isFinBracket

-- LL(1) Dyck grammar:
-- S → ε
--   | [ S ] S
data Balanced : Grammar ℓ-zero where
  nil : ε-grammar ⊢ Balanced
  balanced : literal [ ⊗ (Balanced ⊗ (literal ] ⊗ Balanced)) ⊢ Balanced

mt : String
mt = []

a : String
a = [ ∷ ] ∷ []

a' : String
a' = ] ∷ [ ∷ []

b : String
b = [ ∷ ] ∷ ] ∷ ] ∷ [ ∷ []

c : String
c = ] ∷ ] ∷ ] ∷ [ ∷ []

d : String
d = [ ∷ [ ∷ ] ∷ ] ∷ [ ∷ ] ∷ []

-- Testing the above function is wacky bc of normalization
-- My hacky test is to check if it is a just or is a nothing, which
-- isn't a 100% proof of correctness but gives a sanity check

is-just : ∀ w → (g : Grammar ℓg) → Maybe g w → Bool
is-just w g p = Sum.rec (λ _ → true) (λ _ → false) p

{-# TERMINATING #-}
balanced-parser : Parser Balanced
balanced-parser =
  (fmap (⊗-intro balanced id) ∘g
   (parseChar [ then
   balanced-parser then
   parseChar ] then
   balanced-parser))
  or
  (fmap (⊗-intro Balanced.nil id) ∘g parseε)

_ :
  is-just mt (Balanced ⊗ string-grammar) (balanced-parser mt ⌈ mt ⌉)
    ≡
  true
_ = refl

_ :
  is-just a (Balanced ⊗ string-grammar) (balanced-parser a ⌈ a ⌉)
    ≡
  true
_ = refl

_ :
  is-just a' (Balanced ⊗ string-grammar) (balanced-parser a' ⌈ a' ⌉)
    ≡
  true
_ = refl

is-ε : string-grammar ⊢ Maybe ε-grammar
is-ε = caseKL* char just nothing

-- An intrinsically verified Dyck grammar parser
-- NOTE : This required the addition of a couple things that may be
-- problematic but are likely admissible
-- These are not included in this file, but the code presented here
-- makes use of
-- 1. caseKL*, defined in Grammar.KleeneStar, which cases on if a
--      Kleene star was an nil or a cons. Used in parseChar
-- 2. parseChar, defined in Parser. Which breaks some abstractions
--      to build a primitive character parser, and this is justified
--      when the alphabet is a FinSet
-- 3. ⊤→string, a term ⊤-grammar ⊢ string-grammar. Defined in Parser.
--      Used to define the _or_ parser combinator (also in Parser)
balanced-parser' : string-grammar ⊢ Maybe Balanced
balanced-parser' =
  fmap ⊗-unit-r ∘g
  μ ∘g
  fmap (Maybe⊗r ∘g (⊗-intro id is-ε)) ∘g
  balanced-parser

_ :
  is-just mt Balanced (balanced-parser' mt (⌈ mt ⌉))
    ≡
  true
_ = refl

_ :
  is-just a Balanced (balanced-parser' a (⌈ a ⌉))
    ≡
  true
_ = refl

_ :
  is-just a' Balanced (balanced-parser' a' (⌈ a' ⌉))
    ≡
  false
_ = refl

_ :
  is-just b Balanced (balanced-parser' b (⌈ b ⌉))
    ≡
  false
_ = refl

_ :
  is-just c Balanced (balanced-parser' c (⌈ c ⌉))
    ≡
  false
_ = refl

_ :
  is-just d Balanced (balanced-parser' d (⌈ d ⌉))
    ≡
  true
_ = refl
