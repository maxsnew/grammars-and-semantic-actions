open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import String.Alphabet
module Term.Nullary (Alphabet : Alphabet) where

open import Cubical.Data.List
open import Grammar.Base Alphabet
open import Term.Base Alphabet

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
Element : Grammar ℓA → Type _
Element A = A []

ε⊢ : Grammar ℓA → Type _
ε⊢ = Element

↑ : Grammar ℓA → Type _
↑ = Element

_∘ε_ : A ⊢ B → ε⊢ A → ε⊢ B
(f ∘ε Ap) = f [] Ap
