{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Binary.AsIndexed.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; false ; true)

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsIndexed.Base Alphabet isSetAlphabet
open import Grammar.Sum Alphabet isSetAlphabet
import Grammar.Sum.Binary.AsPrimitive Alphabet isSetAlphabet as AsPrim⊕
open import Term.Base Alphabet isSetAlphabet

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
    @0 AsPrimUnambig : unambiguous (A true AsPrim⊕.⊕ A false)
    AsPrimUnambig = unambiguous≅ (sym≅ (AsPrim⊕.⊕≅⊕Ind A)) unambig⊕

  @0 unambig-⊕-is-disjoint : disjoint (A true) (A false)
  unambig-⊕-is-disjoint = AsPrim⊕.unambig-⊕-is-disjoint AsPrimUnambig

  @0 summand-L-is-unambig : unambiguous (A true)
  summand-L-is-unambig = AsPrim⊕.summand-L-is-unambig AsPrimUnambig

  @0 summand-R-is-unambig : unambiguous (A false)
  summand-R-is-unambig = AsPrim⊕.summand-R-is-unambig AsPrimUnambig

  @0 unambig-summands : (b : Bool) → unambiguous (A b)
  unambig-summands true = summand-L-is-unambig
  unambig-summands false = summand-R-is-unambig
