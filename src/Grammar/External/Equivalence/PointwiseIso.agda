open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.External.Equivalence.PointwiseIso (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (pwIso : ∀ w → Iso (A w) (B w))
  where
  open StrongEquivalence
  open Iso

  opaque
    pointwiseIso→≅ : A ≅ B
    pointwiseIso→≅ .fun w = pwIso w .fun
    pointwiseIso→≅ .inv w = pwIso w .inv
    pointwiseIso→≅ .sec = funExt λ w → funExt (pwIso w .rightInv)
    pointwiseIso→≅ .ret = funExt λ w → funExt (pwIso w .leftInv)
