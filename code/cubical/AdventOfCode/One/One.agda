open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module AdventOfCode.One.One where

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
open import AdventOfCode.One.Input

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

opaque
  unfolding ⌈w⌉→string ⊕ᴰ-distR ⊗-unit-r ⊗-unit-l⁻ ⊤* ⊤ ε ⊗-intro ⊕-elim
  _ : p ≡ ({!false!} , {!!})
  _ = refl

-- in-zero^ : ＂ zero^ ＂ ⊢ num
-- in-zero^ = ⊕-inl

-- in-one^ : ＂ one^ ＂ ⊢ num
-- in-one^ = ⊕-inr ∘g ⊕-inl

-- in-two^ : ＂ two^ ＂ ⊢ num
-- in-two^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-three^ : ＂ three^ ＂ ⊢ num
-- in-three^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-four^ : ＂ four^ ＂ ⊢ num
-- in-four^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-five^ : ＂ five^ ＂ ⊢ num
-- in-five^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-six^ : ＂ six^ ＂ ⊢ num
-- in-six^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-seven^ : ＂ seven^ ＂ ⊢ num
-- in-seven^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-eight^ : ＂ eight^ ＂ ⊢ num
-- in-eight^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inl

-- in-nine^ : ＂ nine^ ＂ ⊢ num
-- in-nine^ = ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊕-inr

-- nums : Grammar ℓ-zero
-- nums = num +

-- whiteChar : Grammar ℓ-zero
-- whiteChar = ＂ SPACE ＂ ⊕ ＂ TAB ＂ ⊕ ＂ NEWLINE ＂

-- in-SPACE : ＂ SPACE ＂ ⊢ whiteChar
-- in-SPACE = ⊕-inl

-- in-TAB : ＂ TAB ＂ ⊢ whiteChar
-- in-TAB = ⊕-inr ∘g ⊕-inl

-- in-NEWLINE : ＂ NEWLINE ＂ ⊢ whiteChar
-- in-NEWLINE = ⊕-inr ∘g ⊕-inr

-- -- open import Test ASCII

-- -- -- p : Maybe.Maybe (goal s)
-- -- -- p = runWeakParser parseGoal s

-- -- q : Maybe.Maybe (＂ zero^ ＂ (mkString "0"))
-- -- q = runWeakParser parseZero (mkString "0")

-- -- opaque
-- --   unfolding ⌈w⌉→string ⊕ᴰ-distR ⊗-unit-r ⊗-unit-l⁻ ⊤* ⊤ ε ⊗-intro internalize' ⊕-elim runWeakParser
-- --   -- _ : p ≡ {!Maybe.just ?!}
-- --   -- _ = refl

-- --   _ : q ≡ {!Maybe.just ?!}
-- --   _ = refl

-- -- open import Grammar.Maybe ASCII
-- -- open StrongEquivalence

-- -- -- parse : string ⊢ Maybe goal
-- -- -- parse = fold*l char λ _ → ⊕ᴰ-elim λ {
-- -- --   nil → nothing ;
-- -- --   snoc →
-- -- --     ⊕ᴰ-elim (λ {
-- -- --         zero^ → addToNum ∘g id ,⊗ in-zero^ ;
-- -- --         one^ → addToNum ∘g id ,⊗ in-one^ ;
-- -- --         two^ → addToNum ∘g id ,⊗ in-two^ ;
-- -- --         three^ → addToNum ∘g id ,⊗ in-three^ ;
-- -- --         four^ → addToNum ∘g id ,⊗ in-four^ ;
-- -- --         five^ → addToNum ∘g id ,⊗ in-five^ ;
-- -- --         six^ → addToNum ∘g id ,⊗ in-six^ ;
-- -- --         seven^ → addToNum ∘g id ,⊗ in-seven^ ;
-- -- --         eight^ → addToNum ∘g id ,⊗ in-eight^ ;
-- -- --         nine^ → addToNum ∘g id ,⊗ in-nine^ ;
-- -- --         SPACE → separate ∘g id ,⊗ in-SPACE ;
-- -- --         TAB → separate ∘g id ,⊗ in-TAB ;
-- -- --         NEWLINE → separate ∘g id ,⊗ in-NEWLINE ;
-- -- --         c → nothing
-- -- --     })
-- -- --     ∘g ⊕ᴰ-distR .fun
-- -- --     ∘g lowerG ,⊗ lowerG}
-- -- --   where
-- -- --   addToNum' : (b : Bool) → ((white ⊗ nums') *) ⊗ num ⊢ (white ⊗ nums') *
-- -- --   addToNum' b =
-- -- --     -- TODO need to flip the arrows ⊸ and ⟜
-- -- --     ⟜-intro⁻ (fold*r _ (λ _ → ⊕ᴰ-elim (λ {
-- -- --       nil → ⟜-intro (
-- -- --         CONS
-- -- --         ∘g (NIL ,⊗ (⊕ᴰ-in b ∘g CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻)) ,⊗ id
-- -- --         ∘g ⊗-unit-l⁻ ,⊗ NIL
-- -- --         ∘g ⊗-unit-r⁻
-- -- --         ∘g ⊗-unit-l
-- -- --         ∘g (lowerG ∘g lowerG) ,⊗ id) ;
-- -- --       cons →
-- -- --         ⟜-intro {!!}
-- -- --         ∘g lowerG ,⊗ lowerG })))

-- -- --   addToNum : Maybe goal ⊗ num ⊢ Maybe goal
-- -- --   addToNum =
-- -- --     fmap (⊕ᴰ-elim (λ b → (⊕ᴰ-in b ∘g id ,⊗ addToNum' b) ∘g ⊗-assoc⁻) ∘g ⊕ᴰ-distL .fun)
-- -- --     ∘g Maybe⊗l

-- -- --   separate : Maybe goal ⊗ whiteChar ⊢ Maybe goal
-- -- --   separate =
-- -- --     fmap {!!}
-- -- --     ∘g Maybe⊗l

-- -- -- -- s' : String ASCIINW
-- -- -- -- s' = Alphabet→SubAlphabet' ASCII NWCharFun s

-- -- -- -- _ : length s' ≡ 10000
-- -- -- -- _ = refl
