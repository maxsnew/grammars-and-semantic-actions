import LambekD.Elab

/-! # Theory definitions for algebraic laws

This module extends the core grammar definitions from `Elab.lean` with
identity, composition, and their basic properties, used by the
`Grammar/` theory modules.
-/

namespace LambekD

open LambekD

variable [AlphabetStr]

-- Grammar morphism identity and composition
def gId (A : Grammar) : A ⊢ A := fun _ a => a

def gComp {A B C : Grammar} (f : B ⊢ C) (g : A ⊢ B) : A ⊢ C := fun w a => f w (g w a)

scoped infixr:80 " ∘g " => gComp

theorem gComp_assoc {A B C D : Grammar} (f : C ⊢ D) (g : B ⊢ C) (h : A ⊢ B) :
    f ∘g (g ∘g h) = (f ∘g g) ∘g h := rfl

theorem gId_comp {A B : Grammar} (f : A ⊢ B) : gId B ∘g f = f := rfl

theorem gComp_id {A B : Grammar} (f : A ⊢ B) : f ∘g gId A = f := rfl

end LambekD
