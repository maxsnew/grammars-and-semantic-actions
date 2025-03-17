open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

is-terminal : Grammar ℓA → Typeω
is-terminal A =
  ∀ {ℓB}{B : Grammar ℓB} → (Σ[ e ∈ B ⊢ A ] (∀ e' → e ≡ e'))

opaque
  ⊤ : Grammar ℓ-zero
  ⊤ _ = Unit

  ⊤* : Grammar ℓA
  ⊤* _ = Unit*

  ⊤-intro :
    A ⊢ ⊤
  ⊤-intro _ _ = tt

  ⊤*-intro : ∀ {ℓB} → A ⊢ ⊤* {ℓB}
  ⊤*-intro _ _ = tt*

  is-terminal-⊤ : is-terminal ⊤
  is-terminal-⊤ = ⊤-intro , (λ e → refl)

  is-terminal-⊤* : ∀ {ℓA} → is-terminal (⊤* {ℓA})
  is-terminal-⊤* = ⊤*-intro , λ _ → refl

