open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Grammar.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    f f' f'' : g ⊢ h
    k : Grammar ℓk
    l : Grammar ℓl

open Iso

-- This can be used in conjunction with isoFunInjective
-- to preserve better goals than a simple cong
LiftDomIso : ∀ {g : Grammar ℓg}{h : Grammar ℓh} ℓ
  → Iso (g ⊢ h) (LiftG ℓ g ⊢ h)
LiftDomIso ℓ .fun e = e ∘g lowerG
LiftDomIso ℓ .inv e = e ∘g liftG
LiftDomIso ℓ .rightInv e = refl
LiftDomIso ℓ .leftInv e = refl

opaque
  unfolding ⊗-intro
  LiftDom⊗Iso :
    ∀ {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
    → (ℓ ℓ' : Level)
    → Iso (g ⊗ k ⊢ h) (LiftG ℓ g ⊗ LiftG ℓ' k ⊢ h)
  LiftDom⊗Iso ℓ ℓ' .fun e = e ∘g (lowerG ,⊗ lowerG)
  LiftDom⊗Iso ℓ ℓ' .inv e = e ∘g liftG ,⊗ liftG
  LiftDom⊗Iso ℓ ℓ' .rightInv e = refl
  LiftDom⊗Iso ℓ ℓ' .leftInv e = refl
