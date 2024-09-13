open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.String Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

⊤ : Grammar ℓ-zero
⊤ _ = Unit

⊤* : Grammar ℓg
⊤* _ = Unit*

⊤-intro :
  g ⊢ ⊤
⊤-intro _ _ = tt

⊤*-intro : ∀ {ℓg} → g ⊢ ⊤* {ℓg}
⊤*-intro _ _ = tt*

⊤→string : ⊤ ⊢ string-grammar
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤*→string : ∀ {ℓg} → ⊤* {ℓg} ⊢ string-grammar
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

is-terminal : Grammar ℓg → Typeω
is-terminal g =
  ∀ {ℓh}{h : Grammar ℓh} → (Σ[ e ∈ h ⊢ g ] (∀ e' → e ≡ e'))

is-terminal-⊤ : is-terminal ⊤
is-terminal-⊤ = ⊤-intro , (λ e → refl)

is-terminal-⊤* : ∀ {ℓg} → is-terminal (⊤* {ℓg})
is-terminal-⊤* = ⊤*-intro , λ _ → refl
