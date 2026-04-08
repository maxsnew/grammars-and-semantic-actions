import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

def gbotElim (A : Grammar Alphabet) : ⊥g ⊢ A := fun _ e => PEmpty.elim e.down

theorem gbot_η {A : Grammar Alphabet} (f g : ⊥g ⊢ A) : f = g := by
  funext w e; exact PEmpty.elim e.down

end LambekD
