{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Nullary (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List
open import Grammar.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

{-- A direct interpretation of terms in an empty (ε) context
 -- ε ⊢ M : k
 --}
Element : Grammar ℓA → Type ℓA
Element A = A []

ε⊢ : Grammar ℓA → Type ℓA
ε⊢ = Element

↑ : Grammar ℓA → Type _
↑ = Element

_∘ε_ : A ⊢ B → ε⊢ A → ε⊢ B
(f ∘ε Ap) = f [] Ap
