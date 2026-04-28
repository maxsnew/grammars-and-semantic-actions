open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.SemanticAction.Monadic (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding (Δ)
open import Term Alphabet
open import Grammar.SemanticAction.Base Alphabet

private
  variable
    ℓ ℓ' ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

pure : ∀ {X : Type ℓ} → X → SemanticAction A X
pure = semact-pure

_>>=_ :
  ∀ {X : Type ℓ} {Y : Type ℓ'}
  → SemanticAction A X
  → (X → SemanticAction B Y)
  → SemanticAction (A ⊗ B) Y
_>>=_ = semact-bind

_<$>_ :
  ∀ {X : Type ℓ} {Y : Type ℓ'}
  → (X → Y) → SemanticAction A X → SemanticAction A Y
_<$>_ = semact-map

infixl 1 _>>=_
infixl 4 _<$>_
