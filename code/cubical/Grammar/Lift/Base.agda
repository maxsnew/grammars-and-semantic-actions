open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
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

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
-- I thought this would be helpful at some point when
-- fiddling with transports,
-- but it's almost surely a bad idea to use univalence directly
LiftG≡ : ∀ ℓ → (g : Grammar ℓ) → g ≡ LiftG ℓ g
LiftG≡ ℓ g i w = ua {A = g w} (LiftEquiv {ℓ' = ℓ}) i

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

module _ ℓ ℓ' (g : Grammar ℓg) where
    LiftG≅2 : g ≅ (LiftG ℓ' (LiftG ℓ g))
    LiftG≅2 =
      LiftG≅ ℓ g 
      ≅∙ LiftG≅ ℓ' (LiftG ℓ g)

isLangLift : isLang g → isLang (LiftG ℓ' g)
isLangLift isLangG w = isOfHLevelLift 1 (isLangG w)

isSetGrammarLift : isSetGrammar g → isSetGrammar (LiftG ℓ' g)
isSetGrammarLift isSetGrammarG w = isOfHLevelLift 2 (isSetGrammarG w)
