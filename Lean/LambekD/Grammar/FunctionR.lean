import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Right linear function: A ⊸ B
-- FunctionR A B w = ∀ w', A w' → B (w' ++ w)
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (B ⊢ A ⊸ C)
def limpRIntro (f : A ⊗ B ⊢ C) : B ⊢ A ⊸ C :=
  fun w b w' a => f (w' ++ w) ⟨splitting w' w, a, b⟩

-- Eval: A ⊗ (A ⊸ B) ⊢ B
def limpRApp : A ⊗ (A ⊸ B) ⊢ B :=
  fun _ ⟨s, a, f⟩ => s.eq ▸ f s.left a

theorem limpR_β (f : A ⊗ B ⊢ C) :
    limpRApp ∘g tensorIntro (gId A) (limpRIntro f) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem limpR_η (f : B ⊢ A ⊸ C) :
    limpRIntro (limpRApp ∘g tensorIntro (gId A) f) = f := rfl

-- Composition with the intro
theorem limpRIntro_comp {D : Grammar Alphabet} (f : A ⊗ B ⊢ C) (g : D ⊢ B) :
    limpRIntro f ∘g g = limpRIntro (f ∘g tensorIntro (gId A) g) := rfl

end LambekD
