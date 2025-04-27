open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.HLevels.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet

private
  variable ℓA ℓB ℓC ℓD : Level

module _ where
  isLang : Grammar ℓA → Type ℓA
  isLang A = ∀ w → isProp (A w)

  isSetGrammar : Grammar ℓA → Type ℓA
  isSetGrammar A = ∀ w → isSet (A w)

  @0 isLang→isSetGrammar : ∀ {A : Grammar ℓA} → isLang A → isSetGrammar A
  isLang→isSetGrammar isLangA w = isProp→isSet (isLangA w)

  Lang : ∀ (ℓA : Level) →  Type (ℓ-suc ℓA)
  Lang ℓA = Σ[ A ∈ Grammar ℓA ] isLang A

  @0 SetGrammar : ∀ (ℓA : Level) →  Type (ℓ-suc ℓA)
  SetGrammar ℓA = Σ[ A ∈ Grammar ℓA ] isSetGrammar A

  @0 Lang→SetGrammar : Lang ℓA → SetGrammar ℓA
  Lang→SetGrammar A = A .fst , isLang→isSetGrammar (A .snd)

  -- Might be confusing but convenient
  ⟨_⟩ : SetGrammar ℓA → Grammar ℓA
  ⟨ A ⟩ = A .fst

  module _ {A : Grammar ℓA} {B : Grammar ℓB} (A≅B : A ≅ B) (isLang-A : isLang A) where
    open StrongEquivalence
    @0 isLang≅ : isLang B
    isLang≅ w x y =
      sym (funExt⁻ (funExt⁻ (A≅B .sec) w) x)
      ∙ cong (A≅B .fun w) (isLang-A w (A≅B .inv w x) (A≅B .inv w y))
      ∙ (funExt⁻ (funExt⁻ (A≅B .sec) w) y)
