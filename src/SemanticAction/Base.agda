open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module SemanticAction.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Parser Alphabet
open import Term Alphabet

private
  variable
    ℓ ℓ' ℓ'' : Level
    X Y : Type ℓ

-- A pure grammar is a constant grammar: the parse trees are always given by the same non-linear type X
Pure : Type ℓ → Grammar ℓ
Pure X = ⊕[ _ ∈ X ] ⊤

Pure-intro :
  ∀ {A : X → Grammar ℓ'}
  → (X → Y)
  → (⊕[ x ∈ X ] A x) ⊢ Pure Y
Pure-intro f = ⊕ᴰ-elim (λ x → σ (f x) ∘g ⊤-intro)  

-- To write a formal grammar and parser
-- 1. Define a formal grammar as a mutual family of inductive datatypes (index X). These define the different sorts of parse trees
-- 2. Define 

-- 2. Define a semantic action as a family of (non-linear) types `Y : X → Type` and an algebra

-- These parts are *specification*.

-- An inductive type of parse trees is given by a functor.
-- A semantic action over an inductive type of parse trees is given by a *non-linear algebra*
module _ {X : Type ℓ} (F : X → Functor X) (Y : X → Type ℓ') where
  SemanticAction : Type (ℓ-max ℓ ℓ')
  SemanticAction = Algebra F λ x → Pure (Y x)

-- Ultimately we only want the semantic result corresponding to the
-- parse tree. *Sometimes* this result is uniquely determined by said
-- parse tree.

-- How to write a sound and complete parser?
