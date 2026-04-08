import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Left linear function: B ⟜ A
-- GFunctionL B A w = ∀ w', A w' → B (w' ++ w)
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (B ⊢ C ⟜ A)
def glimpLIntro (f : A ⊗ B ⊢ C) : B ⊢ C ⟜ A :=
  fun w b w' a => f (w' ++ w) ⟨splitting w' w, a, b⟩

-- Eval: A ⊗ (B ⟜ A) ⊢ B
def glimpLApp : A ⊗ (B ⟜ A) ⊢ B :=
  fun _ ⟨s, a, g⟩ => s.eq ▸ g s.left a

theorem glimpL_β (f : A ⊗ B ⊢ C) :
    glimpLApp ∘g gtensorIntro (gId A) (glimpLIntro f) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem glimpL_η (f : B ⊢ C ⟜ A) :
    glimpLIntro (glimpLApp ∘g gtensorIntro (gId A) f) = f := rfl

-- Composition with the intro
theorem glimpLIntro_comp {D : Grammar Alphabet} (f : A ⊗ B ⊢ C) (g : D ⊢ B) :
    glimpLIntro f ∘g g = glimpLIntro (f ∘g gtensorIntro (gId A) g) := rfl

end LambekD
