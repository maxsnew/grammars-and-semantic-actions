{- Some presentations of the Dyck grammar of balanced parentheses and hopefully some parsers? -}

module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_)
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
  caseKL* char
    -- string empty
    (just ∘g ⊗-intro Balanced.nil KL*.nil ∘g ⊗-unit-r⁻)
    -- string nonempty
    (fmap (⊗-intro balanced id) ∘g
    (parseChar [ then
    balanced-parser then
    parseChar ] then
    balanced-parser) ∘g
    cons)
    -- this cons forgets that we were non empty by putting the string
    -- back together
    -- it can likely be refactored away

_ :
  is-just mt (Balanced ⊗ string-grammar) (balanced-parser mt ⌈ mt ⌉)
    ≡
  true
_ = refl

_ :
  is-just a (Balanced ⊗ string-grammar) (balanced-parser a ⌈ a ⌉)
    ≡
  false
_ = refl

is-ε : string-grammar ⊢ Maybe ε-grammar
is-ε = caseKL* char just nothing

_ :
  is-just mt ε-grammar (is-ε mt (⌈ mt ⌉))
    ≡
  true
_ = refl

_ :
  is-just a ε-grammar (is-ε a (⌈ a ⌉))
    ≡
  false
_ = refl

-- balanced-parser' : Str ⊢ Maybe Balanced
-- balanced-parser' =
--   bind (bind (just ∘g ⊗-unit-r) ∘g
--        Maybe⊗r ∘g
--        functoriality (Balanced ⊗r var) is-ε) ∘g
--   balanced-parser

-- _ :
--   is-just mt Balanced (balanced-parser' mt (⌈ mt ⌉))
--     ≡
--   true
-- _ = refl

-- -- TODO : Some of these tests are failing
-- _ :
--   is-just s Balanced (balanced-parser' s (⌈ s ⌉))
--     ≡
--   false -- should be true
-- _ = refl

-- _ :
--   is-just s' Balanced (balanced-parser' s' (⌈ s' ⌉))
--     ≡
--   false
-- _ = refl

-- _ :
--   is-just s'' Balanced (balanced-parser' s'' (⌈ s'' ⌉))
--     ≡
--   false
-- _ = refl

-- _ :
--   is-just s''' Balanced (balanced-parser' s''' (⌈ s''' ⌉))
--     ≡
--   false -- should be true
-- _ = refl
