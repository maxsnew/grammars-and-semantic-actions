module Examples.Erasure where

open import Erased.Foundations.Prelude
open import Erased.Data.Nat
open import Erased.Data.List
open import Erased.Data.Nat.Properties

open import String.Alphabet

open AlphabetOver

ℕAlph : Alphabet
ℕAlph .fst = ℕ
ℕAlph .snd .is-discrete = discreteℕ

open import Grammar.Base ℕAlph
open import Term.Base ℕAlph
open import Grammar.Literal.Base ℕAlph
open import Grammar.Epsilon.Base ℕAlph
open import Grammar.LinearProduct.Base ℕAlph

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
import Agda.Builtin.String as BuiltinString

postulate
  putStrLn : BuiltinString.String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

s : String
s = 0 ∷ 1 ∷ []

f : ＂ 0 ＂ ⊗ ＂ 1 ＂ ⊢ ((＂ 0 ＂ ⊗ ＂ 1 ＂) ⊗ ε) ⊗ ε
f = ⊗-unit-r⁻ ∘g ⊗-unit-r⁻

g : ((＂ 0 ＂ ⊗ ＂ 1 ＂) ⊗ ε) ⊗ ε ⊢ ＂ 0 ＂ ⊗ ＂ 1 ＂
g = ⊗-unit-r ∘g ⊗-unit-r

h : ＂ 0 ＂ ⊗ ＂ 1 ＂ ⊢ (＂ 0 ＂ ⊗ ε) ⊗ ＂ 1 ＂
h = ⊗-intro ⊗-unit-r⁻ id

opaque
  unfolding _⊗_
  in-parse : (＂ 0 ＂ ⊗ ＂ 1 ＂) s
  in-parse = (((0 ∷ []) , (1 ∷ [])) , refl) , lit-intro , lit-intro

foo : ((＂ 0 ＂ ⊗  ε) ⊗ ＂ 1 ＂) s
foo = (h ∘g g ∘g f) s in-parse


main : IO ⊤
main = putStrLn "Hello, World!"
