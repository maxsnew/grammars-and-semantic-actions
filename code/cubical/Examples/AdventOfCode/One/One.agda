open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Examples.AdventOfCode.One.One where

-- import Agda.Builtin.String as BuiltinStr
-- import IO.Primitive.Core as Prim
-- import Data.Unit.Base as Unit'
-- open import IO
-- open import IO.Finite

open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Maybe as Maybe

open import String.ASCII
open import String.ASCII.NoWhitespace
open import String.Unicode
open import String.SubAlphabet
open import Examples.AdventOfCode.One.Input

open DecodeUnicode ASCII Unicode→ASCII

open import Grammar ASCII
open import Grammar.Maybe ASCII
open import Grammar.String.Properties ASCII
open import Grammar.Equivalence ASCII
open import Grammar.RegularExpression ASCII
open import NFA.Determinization ASCII
open import DFA.Base ASCII
open import DFA.Regex ASCII
open import Term ASCII
open import Helper

private
  module PR = ParseRegex isFinSetASCII

s : String
s = mkString "0"
-- input

num : RegularExpression
num =
  ＂ zero^ ＂r
  ⊕r ＂ one^ ＂r
  -- ⊕r ＂ two^ ＂r
  -- ⊕r ＂ three^ ＂r
  -- ⊕r ＂ four^ ＂r
  -- ⊕r ＂ five^ ＂r
  -- ⊕r ＂ six^ ＂r
  -- ⊕r ＂ seven^ ＂r
  -- ⊕r ＂ eight^ ＂r
  -- ⊕r ＂ nine^ ＂r

nums : RegularExpression
nums = num *r

whiteChar : RegularExpression
whiteChar =
  ＂ SPACE ＂r
  ⊕r ＂ TAB ＂r
  ⊕r ＂ NEWLINE ＂r

white : RegularExpression
white = whiteChar +r

goal : RegularExpression
goal = nums ⊗r ((white ⊗r nums) *r)

goalDFA : DFA
goalDFA = PR.regex→DFA goal

p = PR.run' num s

q = PR.run' (＂ zero^ ＂r) s

opaque
  unfolding _⊕_ ⊕-elim ⊕-inl ⊕-inr ⟜-intro ⊸-intro _⊗_ ⌈w⌉→string ⊕ᴰ-distR ⊗-intro ⊗-in isSetASCII ASCIIChar Determinization.ε-closure Determinization.lit-closure
  _ : p .fst ≡ true
  _ = refl

  -- fast
  _ : q .fst ≡ true
  _ = refl

-- -- TODO : this example takes too long to run
-- opaque
--   unfolding ⊕ᴰ-distR ⊗-intro
-- --   -- ⌈w⌉→string ⊕ᴰ-distR ⊗-unit-r ⊗-unit-l⁻ ⊤* ⊤ ε ⊗-intro ⊕-elim
--   _ : p ≡ (true , ?)
--   _ = refl
