open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.HLevels.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet

private
  variable ℓ ℓG ℓG' ℓH ℓK ℓL : Level

module _ where
  isLang : Grammar ℓG → Type ℓG
  isLang A = ∀ w → isProp (A w)

  isSetGrammar : Grammar ℓG → Type ℓG
  isSetGrammar A = ∀ w → isSet (A w)

  isLang→isSetGrammar : ∀ {A : Grammar ℓG} → isLang A → isSetGrammar A
  isLang→isSetGrammar isLangA w = isProp→isSet (isLangA w)

  Lang : ∀ (ℓ : Level) →  Type (ℓ-suc ℓ)
  Lang ℓ = Σ[ A ∈ Grammar ℓ ] isLang A

  SetGrammar : ∀ (ℓ : Level) →  Type (ℓ-suc ℓ)
  SetGrammar ℓ = Σ[ A ∈ Grammar ℓ ] isSetGrammar A

  Lang→SetGrammar : Lang ℓ → SetGrammar ℓ
  Lang→SetGrammar L = L .fst , isLang→isSetGrammar (L .snd)

  -- Might be confusing but convenient
  ⟨_⟩ : SetGrammar ℓ → Grammar ℓ
  ⟨ A ⟩ = A .fst

  module _ {g : Grammar ℓG} {h : Grammar ℓH} (g≅h : g ≅ h) (isLang-g : isLang g) where
    open StrongEquivalence
    isLang≅ : isLang h
    isLang≅ w x y =
      sym (funExt⁻ (funExt⁻ (g≅h .sec) w) x)
      ∙ cong (g≅h .fun w) (isLang-g w (g≅h .inv w x) (g≅h .inv w y))
      ∙ (funExt⁻ (funExt⁻ (g≅h .sec) w) y)
