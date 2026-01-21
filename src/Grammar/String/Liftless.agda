open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Grammar.String.Liftless (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Inductive.Liftless.Indexed Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

data StrTag : Type ℓ-zero where
  nil : StrTag
  cons : ⟨ Alphabet ⟩ → StrTag

StrF : Unit → Functor Unit
StrF _ = ⊕e StrTag λ where
  nil → k ε
  (cons c) → k (literal c) ⊗e Var _
