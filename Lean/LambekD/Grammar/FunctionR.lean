import LambekD.Grammar.Tensor

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Right linear function: A ⊸ B
-- GFunctionR A B w = ∀ w', A w' → B (w ++ w')
-- ═══════════════════════════════════════════════════════════

-- Curry: (A ⊗ B ⊢ C) → (A ⊢ B ⊸ C)
def glimpRIntro (f : A ⊗ B ⊢ C) : A ⊢ B ⊸ C :=
  fun w a w' b => f (w ++ w') ⟨splitting w w', a, b⟩

-- Eval: (A ⊸ B) ⊗ A ⊢ B
def glimpRApp : (A ⊸ B) ⊗ A ⊢ B :=
  fun _ ⟨s, f, a⟩ => s.eq ▸ f s.right a

theorem glimpR_β (f : A ⊗ B ⊢ C) :
    glimpRApp ∘g gtensorIntro (glimpRIntro f) (gId B) = f := by
  funext w ⟨⟨l, r, eq⟩, a, b⟩
  cases eq with | refl => rfl

theorem glimpR_η (f : A ⊢ B ⊸ C) :
    glimpRIntro (glimpRApp ∘g gtensorIntro f (gId B)) = f := rfl

-- Composition with the intro
theorem glimpRIntro_comp {D : Grammar Alphabet} (f : A ⊗ B ⊢ C) (g : D ⊢ A) :
    glimpRIntro f ∘g g = glimpRIntro (f ∘g gtensorIntro g (gId B)) := rfl

end LambekD
