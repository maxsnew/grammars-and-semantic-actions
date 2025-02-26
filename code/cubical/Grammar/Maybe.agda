open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding (k ; μ)
open import Term Alphabet

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

Maybe : Grammar ℓA → Grammar ℓA
Maybe {ℓA = ℓA} A = A ⊕ ⊤* {ℓA}

just : A ⊢ Maybe A
just = ⊕-inl

nothing : A ⊢ Maybe B
nothing = ⊕-inr ∘g ⊤*-intro

return : A ⊢ Maybe A
return = just

μ : Maybe (Maybe A) ⊢ Maybe A
μ = ⊕-elim id nothing

fmap :
  A ⊢ B →
  Maybe A ⊢ Maybe B
fmap e = ⊕-elim (just ∘g e) nothing

Maybe⊗l : (Maybe A) ⊗ B ⊢ Maybe (A ⊗ B)
Maybe⊗l {A = A}{B = B} =
  ⊸-intro⁻
    (⊕-elim
      (⊸-intro just)
      (⊸-intro (nothing {B = A ⊗ B})))

Maybe⊗r : A ⊗ (Maybe B)  ⊢ Maybe (A ⊗ B)
Maybe⊗r {A = A}{B = B} =
  ⟜-intro⁻
    (⊕-elim
       (⟜-intro just)
       (⟜-intro (nothing {B = A ⊗ B}))
    )

Maybe⊗ : (Maybe A) ⊗ (Maybe B) ⊢ Maybe (A ⊗ B)
Maybe⊗ {A = A}{B = B} =
  ⟜-intro⁻
    (⊕-elim
      (⟜-intro {C = Maybe (A ⊗ B)}
        (⊸-intro⁻
          (⊕-elim
            (⊸-intro just)
            (⊸-intro (nothing {B = A ⊗ B})))))
      (⟜-intro (nothing {B = A ⊗ B})))
