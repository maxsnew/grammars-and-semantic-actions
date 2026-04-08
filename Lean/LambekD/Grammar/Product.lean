import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C : Grammar Alphabet}

def gprodProj₁ : A & B ⊢ A := fun w ⟨a, _⟩ => a

def gprodProj₂ : A & B ⊢ B := fun w ⟨_, b⟩ => b

def gprodIntro (f : C ⊢ A) (g : C ⊢ B) : C ⊢ A & B :=
  fun w c => ⟨f w c, g w c⟩

def gdiagonal : A ⊢ A & A := gprodIntro (gId A) (gId A)

theorem gprod_β₁ (f : C ⊢ A) (g : C ⊢ B) : gprodProj₁ ∘g gprodIntro f g = f := rfl

theorem gprod_β₂ (f : C ⊢ A) (g : C ⊢ B) : gprodProj₂ ∘g gprodIntro f g = g := rfl

theorem gprod_η (f : C ⊢ A & B) : gprodIntro (gprodProj₁ ∘g f) (gprodProj₂ ∘g f) = f := rfl

theorem gprodIntro_comp (f : C ⊢ A) (g : C ⊢ B) {D : Grammar Alphabet} (h : D ⊢ C) :
    gprodIntro f g ∘g h = gprodIntro (f ∘g h) (g ∘g h) := rfl

end LambekD
