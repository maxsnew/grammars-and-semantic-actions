import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

def gsumInl : A ⊢ A ⊕ B := fun w a => _root_.Sum.inl a

def gsumInr : B ⊢ A ⊕ B := fun w b => _root_.Sum.inr b

def gsumElim (f : A ⊢ C) (g : B ⊢ C) : A ⊕ B ⊢ C :=
  fun w s => match s with | .inl a => f w a | .inr b => g w b

theorem gsum_βl (f : A ⊢ C) (g : B ⊢ C) : gsumElim f g ∘g gsumInl = f := rfl

theorem gsum_βr (f : A ⊢ C) (g : B ⊢ C) : gsumElim f g ∘g gsumInr = g := rfl

theorem gsum_η (f : A ⊕ B ⊢ C) : gsumElim (f ∘g gsumInl) (f ∘g gsumInr) = f := by
  funext w s; cases s <;> rfl

theorem gsumElim_comp (f : A ⊢ C) (g : B ⊢ C) {D : Grammar Alphabet} (h : C ⊢ D) :
    h ∘g gsumElim f g = gsumElim (h ∘g f) (h ∘g g) := by
  funext w s; cases s <;> rfl

-- Distributivity
def gtensorSumDistL : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C) :=
  fun w ⟨s, a, bc⟩ => match bc with
  | .inl b => .inl ⟨s, a, b⟩
  | .inr c => .inr ⟨s, a, c⟩

def gtensorSumDistR : (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C) :=
  fun w ⟨s, ab, c⟩ => match ab with
  | .inl a => .inl ⟨s, a, c⟩
  | .inr b => .inr ⟨s, b, c⟩

end LambekD
