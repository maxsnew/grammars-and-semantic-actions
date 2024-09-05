open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{-- Embed the linear typing rules
 -- These correspond to terms like x : g ⊢ M : g'
 -- with the caveat that derivations
 -- x : g , y : h ⊢ M : g'
 -- are represented as
 -- x : g ⊗ h ⊢ M : g'
 --
 -- Likewise, we represent the empty context with the empty grammar
 -- ∙ ⊢ M : g
 -- is given as
 -- x : ε-grammar ⊢ M : g
 --}
module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  where
  Term : Type (ℓ-max ℓg ℓh)
  Term = ∀ w → g w → h w

  infix 5 Term
  syntax Term g g' = g ⊢ g'
