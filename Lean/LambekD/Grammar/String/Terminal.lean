import LambekD.Grammar.String.Base

/-!
# The read axiom and string ≅ ⊤

Postulates the `read` axiom (Axiom 3.4 from the paper):
every string can be parsed by the `string` grammar, and
`string ≅ ⊤` as a strong equivalence.

Ports `Grammar.String.Terminal` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

/-- **Axiom 3.4 (Read)**: The terminal grammar `⊤` maps into `string`.
    Every string can be read — this axiom asserts that the grammar
    `string` accepts all strings. -/
def read : (⊤g : Grammar Alphabet) ⊢ string :=
  fun w _ => mkString w

/-- Introduction rule: `⊤ ⊢ string`. -/
def stringIntro : (⊤g : Grammar Alphabet) ⊢ string := read

-- The string grammar is isomorphic to the terminal grammar.
-- Forward direction: `string ⊢ ⊤` (trivially, since `⊤` accepts everything).
-- Inverse: `⊤ ⊢ string` (via `read`).
-- (Full strong equivalence proof requires unambiguity of string and ⊤.)

end LambekD
