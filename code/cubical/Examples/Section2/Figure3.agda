module Examples.Section2.Figure3 where

open import Examples.Section2.Alphabet
open import Grammar Alphabet
open import Term Alphabet

g : ＂ a ＂ ⊗ ＂ b ＂ ⊢ (＂ a ＂ *) ⊗ ＂ b ＂ ⊕ ＂ c ＂
g = inl ∘g (CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id

-- *-singleton is just a synonym for the above combinator
-- CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻
g' : ＂ a ＂ ⊗ ＂ b ＂ ⊢ (＂ a ＂ *) ⊗ ＂ b ＂ ⊕ ＂ c ＂
g' = inl ∘g *-singleton ＂ a ＂ ,⊗ id
