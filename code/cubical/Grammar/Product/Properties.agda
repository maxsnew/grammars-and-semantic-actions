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
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open StrongEquivalence

&unambiguous :
  unambiguous g →
  unambiguous h →
  unambiguous (g & h)
&unambiguous ug uh e e' =
  &≡ e e' (ug _ _) (uh _ _)
