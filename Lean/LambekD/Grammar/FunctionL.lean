import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Left linear function: B ⟜ A
-- FunctionL B A w = ∀ w', A w' → B (w' ++ w)
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (B ⊢ C ⟜ A)
def limpLIntro (f : A ⊗ B ⊢ C) : B ⊢ C ⟜ A :=
  fun w b w' a => f (w' ++ w) ⟨splitting w' w, a, b⟩

-- Eval: A ⊗ (B ⟜ A) ⊢ B
def limpLApp : A ⊗ (B ⟜ A) ⊢ B :=
  fun _ ⟨s, a, g⟩ => s.eq ▸ g s.left a

theorem limpL_β (f : A ⊗ B ⊢ C) :
    limpLApp ∘g tensorIntro (gId A) (limpLIntro f) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem limpL_η (f : B ⊢ C ⟜ A) :
    limpLIntro (limpLApp ∘g tensorIntro (gId A) f) = f := rfl

-- Composition with the intro
theorem limpLIntro_comp {D : Grammar Alphabet} (f : A ⊗ B ⊢ C) (g : D ⊢ B) :
    limpLIntro f ∘g g = limpLIntro (f ∘g tensorIntro (gId A) g) := rfl

end LambekD
