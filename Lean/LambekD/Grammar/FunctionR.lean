import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Right linear function: A ⊸ B
-- FunctionR A B w = ∀ w', A w' → B (w ++ w')
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (A ⊢ B ⊸ C)
def limpRIntro (f : A ⊗ B ⊢ C) : A ⊢ B ⊸ C :=
  fun w a w' b => f (w ++ w') ⟨splitting w w', a, b⟩

-- Eval: (A ⊸ B) ⊗ A ⊢ B
def limpRApp : (A ⊸ B) ⊗ A ⊢ B :=
  fun _ ⟨s, f, a⟩ => s.eq ▸ f s.right a

theorem limpR_β (f : A ⊗ B ⊢ C) :
    limpRApp ∘g tensorIntro (limpRIntro f) (gId B) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem limpR_η (f : A ⊢ B ⊸ C) :
    limpRIntro (limpRApp ∘g tensorIntro f (gId B)) = f := rfl

-- Composition with the intro
theorem limpRIntro_comp {D : Grammar Alphabet} (f : A ⊗ B ⊢ C) (g : D ⊢ A) :
    limpRIntro f ∘g g = limpRIntro (f ∘g tensorIntro g (gId B)) := rfl

end LambekD
