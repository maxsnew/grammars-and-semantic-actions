open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

&unambiguous :
  unambiguous A →
  unambiguous B →
  unambiguous (A & B)
&unambiguous uA uB e e' =
  &≡ e e' (uA _ _) (uB _ _)
