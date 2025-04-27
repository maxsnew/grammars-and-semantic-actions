{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

@0 is-terminal : Grammar ℓA → Typeω
is-terminal A =
  ∀ {ℓB}{B : Grammar ℓB} → (Σ[ e ∈ B ⊢ A ] (∀ e' → e ≡ e'))

opaque
  ⊤ : Grammar ℓ-zero
  ⊤ _ = Unit

  @0 ⊤* : Grammar ℓA
  ⊤* _ = Unit*

  ⊤-intro :
    A ⊢ ⊤
  ⊤-intro _ _ = tt

  @0 ⊤*-intro : ∀ {ℓB} → A ⊢ ⊤* {ℓB}
  ⊤*-intro _ _ = tt*

  @0 is-terminal-⊤ : is-terminal ⊤
  is-terminal-⊤ = ⊤-intro , (λ e → refl)

  @0 is-terminal-⊤* : ∀ {ℓA} → is-terminal (⊤* {ℓA})
  is-terminal-⊤* = ⊤*-intro , λ _ → refl
