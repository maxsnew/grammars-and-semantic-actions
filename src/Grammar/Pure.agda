open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Pure (Alphabet : hSet ℓ-zero) where

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

-- A pure grammar is a constant grammar: the parse trees are always
-- given by the same non-linear type X
Pure : Type ℓ → Grammar ℓ
Pure X = ⊕[ _ ∈ X ] ⊤

Pure-intro :
  ∀ {A : X → Grammar ℓ'}
  → (X → Y)
  → (⊕[ x ∈ X ] A x) ⊢ Pure Y
Pure-intro f = ⊕ᴰ-elim (λ x → σ (f x) ∘g ⊤-intro)  
