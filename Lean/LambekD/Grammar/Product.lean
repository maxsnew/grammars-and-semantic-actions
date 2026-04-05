import LambekD.Defs

namespace LambekD

open LambekD

variable [AlphabetStr]
variable {A B C : Grammar}

def prodProj₁ : A & B ⊢ A := fun w ⟨a, _⟩ => a

def prodProj₂ : A & B ⊢ B := fun w ⟨_, b⟩ => b

def prodIntro (f : C ⊢ A) (g : C ⊢ B) : C ⊢ A & B :=
  fun w c => ⟨f w c, g w c⟩

def diagonal : A ⊢ A & A := prodIntro (gId A) (gId A)

theorem prod_β₁ (f : C ⊢ A) (g : C ⊢ B) : prodProj₁ ∘g prodIntro f g = f := rfl

theorem prod_β₂ (f : C ⊢ A) (g : C ⊢ B) : prodProj₂ ∘g prodIntro f g = g := rfl

theorem prod_η (f : C ⊢ A & B) : prodIntro (prodProj₁ ∘g f) (prodProj₂ ∘g f) = f := rfl

theorem prodIntro_comp (f : C ⊢ A) (g : C ⊢ B) {D : Grammar} (h : D ⊢ C) :
    prodIntro f g ∘g h = prodIntro (f ∘g h) (g ∘g h) := rfl

end LambekD
