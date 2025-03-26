module Examples.Section2.Figure4 where

open import Examples.Section2.Alphabet
open import Grammar Alphabet
open import Term Alphabet

h : (＂ a ＂ ⊗ ＂ a ＂) * ⊢ ＂ a ＂ *
h = fold*r (＂ a ＂ ⊗ ＂ a ＂)
  -- nil case : ε ⊢ ＂ a ＂ *
  NIL
  -- cons case : (＂ a ＂ ⊗ ＂ a ＂) ⊗ (＂ a ＂ *) ⊢ ＂ a ＂ *
  (CONS
  ∘g id ,⊗ CONS -- turn the left side of the ⊗ into an ＂ a ＂ *
  ∘g ⊗-assoc⁻ -- reassociate to ＂ a ＂ ⊗ (＂ a ＂ ⊗ ＂ a ＂ *)
  )
