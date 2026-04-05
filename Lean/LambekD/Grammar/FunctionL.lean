import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

variable [AlphabetStr]
variable {A B C : Grammar}

-- ═══════════════════════════════════════════════════════════
-- Left linear function: B ⟜ A
-- FunctionL B A w = ∀ w', A w' → B (w ++ w')
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (A ⊢ C ⟜ B)
def limpLIntro (f : A ⊗ B ⊢ C) : A ⊢ C ⟜ B :=
  fun w a w' b => f (w ++ w') ⟨splitting w w', a, b⟩

-- Eval: (B ⟜ A) ⊗ A ⊢ B
def limpLApp : (B ⟜ A) ⊗ A ⊢ B :=
  fun _ ⟨s, f, a⟩ => s.eq ▸ f s.right a

theorem limpL_β (f : A ⊗ B ⊢ C) :
    limpLApp ∘g tensorIntro (limpLIntro f) (gId B) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem limpL_η (f : A ⊢ C ⟜ B) :
    limpLIntro (limpLApp ∘g tensorIntro f (gId B)) = f := rfl

-- Composition with the intro
theorem limpLIntro_comp {D : Grammar} (f : A ⊗ B ⊢ C) (g : D ⊢ A) :
    limpLIntro f ∘g g = limpLIntro (f ∘g tensorIntro g (gId B)) := rfl

end LambekD
