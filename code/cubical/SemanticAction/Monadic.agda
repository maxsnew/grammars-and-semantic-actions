open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

module SemanticAction.Monadic (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (map)
open import Grammar.String.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term Alphabet
open import SemanticAction.Base Alphabet

private
  variable
    A B : Type _
    g h : Grammar _

pure = semact-pure
_>>=_ = semact-bind

map-g = semact-map-g

map : (A → B) → SemanticAction g A → SemanticAction g B
map f x = map-g ⊗-unit-r⁻ do
  a ← x
  pure (f a)

_<$>_ = map

