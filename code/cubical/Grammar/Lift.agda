{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

LiftG : ∀ ℓ' → Grammar ℓ → Grammar (ℓ-max ℓ ℓ')
LiftG ℓ' g w = Lift {j = ℓ'} (g w)

liftG : g ⊢ LiftG ℓ' g
liftG = λ w z → lift z

lowerG : LiftG ℓ' g ⊢ g
lowerG = λ w z → z .lower

open StrongEquivalence
module _ ℓ (g : Grammar ℓg) where
  LiftG≅ : StrongEquivalence g (LiftG ℓ g)
  LiftG≅ .fun = liftG
  LiftG≅ .inv = lowerG
  LiftG≅ .sec = refl
  LiftG≅ .ret = refl
