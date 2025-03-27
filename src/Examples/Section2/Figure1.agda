module Examples.Section2.Figure1 where

open import Examples.Section2.Alphabet
open import Grammar Alphabet
open import Term Alphabet

f : ＂ a ＂ ⊗ ＂ b ＂ ⊢ ＂ a ＂ ⊗ ＂ b ＂ ⊕ ＂ c ＂
f = inl
