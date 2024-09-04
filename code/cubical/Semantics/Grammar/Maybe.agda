open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Maybe ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar(Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

Maybe : Grammar ℓg → Grammar ℓg
Maybe {ℓg = ℓg} g = g ⊕ ⊤-grammar {ℓg}

-- TODO : just and nothing might not be the right names here
just : g ⊢ Maybe g
just = ⊕-inl

nothing : g ⊢ Maybe h
nothing = ⊕-inr ∘g ⊤-intro

bind :
  g ⊢ Maybe h →
  Maybe g ⊢ Maybe h
bind e = ⊕-elim e nothing

Maybe⊗l : (Maybe g) ⊗ h ⊢ Maybe (g ⊗ h)
Maybe⊗l {g = g}{h = h} =
  ⟜-intro⁻
    (⊕-elim
      (⟜-intro just)
      (⟜-intro (nothing {h = g ⊗ h})))

Maybe⊗r : g ⊗ (Maybe h)  ⊢ Maybe (g ⊗ h)
Maybe⊗r {g = g}{h = h} =
  -⊗-intro⁻
    (⊕-elim
       (-⊗-intro just)
       (-⊗-intro (nothing {h = g ⊗ h}))
    )

Maybe⊗ : (Maybe g) ⊗ (Maybe h) ⊢ Maybe (g ⊗ h)
Maybe⊗ {g = g}{h = h} =
  -⊗-intro⁻
    (⊕-elim
      (-⊗-intro {k = Maybe (g ⊗ h)}
        (⟜-intro⁻
          (⊕-elim
            (⟜-intro just)
            (⟜-intro (nothing {h = g ⊗ h})))))
      (-⊗-intro (nothing {h = g ⊗ h})))
