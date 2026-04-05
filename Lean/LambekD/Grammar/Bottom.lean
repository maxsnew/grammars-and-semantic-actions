import LambekD.Defs

namespace LambekD

open LambekD

variable [AlphabetStr]

def botElim (A : Grammar) : ⊥g ⊢ A := fun _ e => PEmpty.elim e.down

theorem bot_η {A : Grammar} (f g : ⊥g ⊢ A) : f = g := by
  funext w e; exact PEmpty.elim e.down

end LambekD
