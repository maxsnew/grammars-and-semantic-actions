{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.AsEquality (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  ε : Grammar ℓ-zero
  ε w = w Eq.≡ []

  ε-intro : ε⊢ ε
  ε-intro = Eq.refl

  ε-elim : ∀ {A : Grammar ℓA} → ε⊢ A → ε ⊢ A
  ε-elim {A = A} A[] w Eq.refl = A[]

  @0 ε-elim-natural : ∀ {A : Grammar ℓA} → (a : ε⊢ A) →
    (f : A ⊢ B) →
    f ∘g ε-elim {A = A} a ≡ ε-elim (f ∘ε a)
  ε-elim-natural {B = B} {A = A} _ _ = funExt λ w → funExt λ where Eq.refl → refl

  @0 ε-β : ∀ (Ap : ε⊢ A) → ε-elim {A = A} Ap ∘ε ε-intro ≡ Ap
  ε-β {A = A} Ap = refl

  @0 isLangε : isLang ε
  isLangε w Eq.refl Eq.refl = refl

  @0 isSetGrammarε : isSetGrammar ε
  isSetGrammarε = isLang→isSetGrammar isLangε

  @0 ε-length0 : ∀ w → ε w → length w ≡ 0
  ε-length0 [] p = refl
  ε-length0 (x ∷ w) ()

ε* : ∀ {ℓ : Level} → Grammar ℓ
ε* {ℓ = ℓ} = LiftG ℓ ε

@0 isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
isLangε* = isLangLift isLangε

@0 isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
isSetGrammarε* = isLang→isSetGrammar isLangε*
