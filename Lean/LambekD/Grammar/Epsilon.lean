import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

def εIntro : Epsilon ([] : String Alphabet) := ⟨PLift.up rfl⟩

end LambekD
