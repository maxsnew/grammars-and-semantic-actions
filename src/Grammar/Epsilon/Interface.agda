open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.Interface (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

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

record εStr : Typeω where
  field
    ε : Grammar ℓ-zero
    ε-intro : ε⊢ ε
    ε-elim : ∀ {A : Grammar ℓA} → ε⊢ A → ε ⊢ A
    @0 ε-elim-natural :
      ∀ {A : Grammar ℓA} → (a : ε⊢ A) →
      (f : A ⊢ B) →
      f ∘g ε-elim {A = A} a ≡ ε-elim (f ∘ε a)
    @0 ε-β : ∀ (Ap : ε⊢ A) → ε-elim {A = A} Ap ∘ε ε-intro ≡ Ap
    @0 isLangε : isLang ε
    @0 ε-length0 : ∀ w → ε w → length w ≡ 0

  @0 isSetGrammarε : isSetGrammar ε
  isSetGrammarε = isLang→isSetGrammar isLangε

  ε* : ∀ {ℓ : Level} → Grammar ℓ
  ε* {ℓ = ℓ} = LiftG ℓ ε

  @0 isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
  isLangε* = isLangLift isLangε

  @0 isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
  isSetGrammarε* = isLang→isSetGrammar isLangε*

open εStr {{...}} public
