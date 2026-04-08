import LambekD.Core.Defs

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

def gεIntro : GEpsilon ([] : String Alphabet) := ⟨PLift.up rfl⟩

end LambekD
