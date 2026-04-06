import LambekD.Core.Defs

/-! # Grammar properties: unambiguity and disjointness -/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

/-- A grammar is **unambiguous** if at most one parse tree per string. -/
def Unambiguous (A : Grammar Alphabet) : Prop :=
  ∀ w (a₁ a₂ : A w), a₁ = a₂

/-- Two grammars are **disjoint** if no string is parsed by both. -/
def Disjoint (A B : Grammar Alphabet) : Prop :=
  ∀ w, A w → B w → False

end LambekD
