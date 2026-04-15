open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

LiftG : ∀ ℓB → Grammar ℓA → Grammar (ℓ-max ℓA ℓB)
LiftG ℓB A w = Lift ℓB (A w)

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
-- I thought this would be helpful at some point when
-- fiddling with transports,
-- but it's almost surely a bad idea to use univalence directly
LiftG≡ : ∀ ℓA → (A : Grammar ℓA) → A ≡ LiftG ℓA A
LiftG≡ ℓA A i w = ua {A = A w} (LiftEquiv {ℓ' = ℓA}) i

liftG : A ⊢ LiftG ℓB A
liftG = λ w z → lift z

lowerG : LiftG ℓB A ⊢ A
lowerG = λ w z → z .lower

open StrongEquivalence
module _ ℓB (A : Grammar ℓA) where
  LiftG≅ : A ≅ (LiftG ℓB A)
  LiftG≅ .fun = liftG
  LiftG≅ .inv = lowerG
  LiftG≅ .sec = refl
  LiftG≅ .ret = refl

module _ ℓB ℓC (A : Grammar ℓA) where
    LiftG≅2 : A ≅ (LiftG ℓC (LiftG ℓB A))
    LiftG≅2 =
      LiftG≅ ℓB A
      ≅∙ LiftG≅ ℓC (LiftG ℓB A)

isLangLift : isLang A → isLang (LiftG ℓB A)
isLangLift isLangA w = isOfHLevelLift 1 (isLangA w)

isSetGrammarLift : isSetGrammar A → isSetGrammar (LiftG ℓB A)
isSetGrammarLift isSetGrammarA w = isOfHLevelLift 2 (isSetGrammarA w)
