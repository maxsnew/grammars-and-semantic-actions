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
open import DFA.Base ASCII
open import DFA.Regex ASCII
open import Term ASCII
open import Helper

private
  module PR = ParseRegex (isFinSetFin {n = 97})

s : String
s = mkString input

s' : string s
s' = mkstring s

num : RegularExpression
num =
  ＂ zero^ ＂r
  ⊕r ＂ one^ ＂r
  ⊕r ＂ two^ ＂r
  ⊕r ＂ three^ ＂r
  ⊕r ＂ four^ ＂r
  ⊕r ＂ five^ ＂r
  ⊕r ＂ six^ ＂r
  ⊕r ＂ seven^ ＂r
  ⊕r ＂ eight^ ＂r
  ⊕r ＂ nine^ ＂r

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

p : (⊕[ b ∈ Bool ] PR.Trace goal b (PR.init goal)) s
p = PR.run goal s s'

-- TODO : this example takes too long to run
-- opaque
--   unfolding mkstring ⊕ᴰ-distR ⊗-intro
--   -- ⌈w⌉→string ⊕ᴰ-distR ⊗-unit-r ⊗-unit-l⁻ ⊤* ⊤ ε ⊗-intro ⊕-elim
--   _ : p ≡ (true , ?)
--   _ = refl
