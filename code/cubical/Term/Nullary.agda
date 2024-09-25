open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Nullary (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{-- A direct interpretation of terms in an empty (ε) context
 -- ε ⊢ M : k
 --}
Element : Grammar ℓg → Type _
Element g = g []

ε⊢ : Grammar ℓg → Type _
ε⊢ = Element

_∘ε_ : g ⊢ h → ε⊢ g → ε⊢ h
(f ∘ε gp) = f [] gp
