open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Grammar.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open Iso

-- This can be used in conjunction with isoFunInjective
-- to preserve better goals than a simple cong
LiftDomIso : ∀ {A : Grammar ℓA}{B : Grammar ℓB} ℓC
  → Iso (A ⊢ B) (LiftG ℓC A ⊢ B)
LiftDomIso ℓC .fun e = e ∘g lowerG
LiftDomIso ℓC .inv e = e ∘g liftG
LiftDomIso ℓC .sec e = refl
LiftDomIso ℓC .ret e = refl

opaque
  unfolding ⊗-intro
  LiftDom⊗Iso :
    ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
    → (ℓD ℓE : Level)
    → Iso (A ⊗ C ⊢ B) (LiftG ℓD A ⊗ LiftG ℓE C ⊢ B)
  LiftDom⊗Iso ℓD ℓE .fun e = e ∘g (lowerG ,⊗ lowerG)
  LiftDom⊗Iso ℓD ℓE .inv e = e ∘g liftG ,⊗ liftG
  LiftDom⊗Iso ℓD ℓE .sec e = refl
  LiftDom⊗Iso ℓD ℓE .ret e = refl

open StrongEquivalence
module _ ℓC ℓD (A : Grammar ℓA) (B : Grammar ℓB) where
  LiftG⊗LiftG≅ : (A ⊗ B) ≅ (LiftG ℓC A ⊗ LiftG ℓD B)
  LiftG⊗LiftG≅ .fun = liftG ,⊗ liftG
  LiftG⊗LiftG≅ .inv = lowerG ,⊗ lowerG
  LiftG⊗LiftG≅ .sec = the-sec
    where
    opaque
      unfolding ⊗-intro
      the-sec : LiftG⊗LiftG≅ .fun ∘g LiftG⊗LiftG≅ .inv ≡ id
      the-sec = refl
  LiftG⊗LiftG≅ .ret = the-ret
    where
    opaque
      unfolding ⊗-intro
      the-ret : LiftG⊗LiftG≅ .inv ∘g LiftG⊗LiftG≅ .fun ≡ id
      the-ret = refl
