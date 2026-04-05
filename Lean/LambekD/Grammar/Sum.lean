import LambekD.Defs

namespace LambekD

open LambekD

variable [AlphabetStr]
variable {A B C : Grammar}

def sumInl : A ⊢ A ⊕ B := fun w a => _root_.Sum.inl a

def sumInr : B ⊢ A ⊕ B := fun w b => _root_.Sum.inr b

def sumElim (f : A ⊢ C) (g : B ⊢ C) : A ⊕ B ⊢ C :=
  fun w s => match s with | .inl a => f w a | .inr b => g w b

theorem sum_βl (f : A ⊢ C) (g : B ⊢ C) : sumElim f g ∘g sumInl = f := rfl

theorem sum_βr (f : A ⊢ C) (g : B ⊢ C) : sumElim f g ∘g sumInr = g := rfl

theorem sum_η (f : A ⊕ B ⊢ C) : sumElim (f ∘g sumInl) (f ∘g sumInr) = f := by
  funext w s; cases s <;> rfl

theorem sumElim_comp (f : A ⊢ C) (g : B ⊢ C) {D : Grammar} (h : C ⊢ D) :
    h ∘g sumElim f g = sumElim (h ∘g f) (h ∘g g) := by
  funext w s; cases s <;> rfl

-- Distributivity
def tensorSumDistL : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C) :=
  fun w ⟨s, a, bc⟩ => match bc with
  | .inl b => .inl ⟨s, a, b⟩
  | .inr c => .inr ⟨s, a, c⟩

def tensorSumDistR : (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C) :=
  fun w ⟨s, ab, c⟩ => match ab with
  | .inl a => .inl ⟨s, a, c⟩
  | .inr b => .inr ⟨s, b, c⟩

end LambekD
