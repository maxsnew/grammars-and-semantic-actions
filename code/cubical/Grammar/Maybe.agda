open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding (k ; μ)
open import Term Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

Maybe : Grammar ℓg → Grammar ℓg
Maybe {ℓg = ℓg} g = g ⊕ ⊤* {ℓg}

just : g ⊢ Maybe g
just = ⊕-inl

nothing : g ⊢ Maybe h
nothing = ⊕-inr ∘g ⊤*-intro

return : g ⊢ Maybe g
return = just

μ : Maybe (Maybe g) ⊢ Maybe g
μ = ⊕-elim id nothing

fmap :
  g ⊢ h →
  Maybe g ⊢ Maybe h
fmap e = ⊕-elim (just ∘g e) nothing

Maybe⊗l : (Maybe g) ⊗ h ⊢ Maybe (g ⊗ h)
Maybe⊗l {g = g}{h = h} =
  ⊸-intro⁻
    (⊕-elim
      (⊸-intro just)
      (⊸-intro (nothing {h = g ⊗ h})))

Maybe⊗r : g ⊗ (Maybe h)  ⊢ Maybe (g ⊗ h)
Maybe⊗r {g = g}{h = h} =
  ⟜-intro⁻
    (⊕-elim
       (⟜-intro just)
       (⟜-intro (nothing {h = g ⊗ h}))
    )

Maybe⊗ : (Maybe g) ⊗ (Maybe h) ⊢ Maybe (g ⊗ h)
Maybe⊗ {g = g}{h = h} =
  ⟜-intro⁻
    (⊕-elim
      (⟜-intro {k = Maybe (g ⊗ h)}
        (⊸-intro⁻
          (⊕-elim
            (⊸-intro just)
            (⊸-intro (nothing {h = g ⊗ h})))))
      (⟜-intro (nothing {h = g ⊗ h})))
