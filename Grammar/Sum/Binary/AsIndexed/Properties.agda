open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Binary.AsIndexed.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Bool using (Bool ; false ; true)

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Binary.AsIndexed.Base Alphabet
open import Grammar.Sum Alphabet
import Grammar.Sum.Binary.AsPrimitive Alphabet as AsPrim⊕
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD  : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module _ {A : Bool → Grammar ℓA} (unambig⊕ : unambiguous (⊕ᴰ A)) where
  private
    AsPrimUnambig : unambiguous (A true AsPrim⊕.⊕ A false)
    AsPrimUnambig = unambiguous≅ (sym≅ (AsPrim⊕.⊕≅⊕Ind A)) unambig⊕

  unambig-⊕-is-disjoint : disjoint (A true) (A false)
  unambig-⊕-is-disjoint = AsPrim⊕.unambig-⊕-is-disjoint AsPrimUnambig

  summand-L-is-unambig : unambiguous (A true)
  summand-L-is-unambig = AsPrim⊕.summand-L-is-unambig AsPrimUnambig

  summand-R-is-unambig : unambiguous (A false)
  summand-R-is-unambig = AsPrim⊕.summand-R-is-unambig AsPrimUnambig

  unambig-summands : (b : Bool) → unambiguous (A b)
  unambig-summands true = summand-L-is-unambig
  unambig-summands false = summand-R-is-unambig
