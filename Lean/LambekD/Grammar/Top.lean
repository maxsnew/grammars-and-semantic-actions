import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

def topIntro (A : Grammar Alphabet) : A ⊢ ⊤g := fun _ _ => ⟨PUnit.unit⟩

theorem top_η {A : Grammar Alphabet} (f g : A ⊢ ⊤g) : f = g := by
  funext w a
  have : f w a = ⟨PUnit.unit⟩ := by cases f w a with | up u => cases u; rfl
  have : g w a = ⟨PUnit.unit⟩ := by cases g w a with | up u => cases u; rfl
  simp_all

end LambekD
