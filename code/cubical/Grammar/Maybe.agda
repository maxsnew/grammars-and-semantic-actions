open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet
open import String.More Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

Maybe : Grammar ℓg → Grammar ℓg
Maybe {ℓg = ℓg} g = g ⊕ ⊤-grammar {ℓg}

just : g ⊢ Maybe g
just = ⊕-inl

nothing : g ⊢ Maybe h
nothing = ⊕-inr ∘g ⊤-intro

return : g ⊢ Maybe g
return = just

μ : Maybe (Maybe g) ⊢ Maybe g
μ = ⊕-elim id nothing

fmap :
  g ⊢ h →
  Maybe g ⊢ Maybe h
fmap e = ⊕-elim (just ∘g e) nothing

-- -- Kleisli composition
-- _∘K_ : g ⊢ Maybe h → k ⊢ Maybe g → k ⊢ Maybe h
-- (e ∘K e') = μ ∘g fmap e ∘g e'
-- infixr 8 _∘K_


-- _⋆P_ : Paresr



-- bind :
--   g ⊢ Maybe h →
--   Maybe g ⊢ Maybe h
-- bind e = ⊕-elim e nothing

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
