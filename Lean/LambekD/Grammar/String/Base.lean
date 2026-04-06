import LambekD.Grammar.KleeneStar.Base

/-!
# Characters and strings as grammars

Defines `char` (any single character) and `string` (sequence of characters)
as grammars, with canonical parse constructors.

Ports `Grammar.String.Base` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

/-- The grammar that accepts any single character from the alphabet.
    Defined as the indexed coproduct over all characters of the literal grammar. -/
def char : Grammar Alphabet := ⊕[c ∈ Alphabet] lit(c)

/-- The grammar that accepts any string. Defined as `char *` (Kleene star of characters). -/
def string : Grammar Alphabet := char *

/-- The grammar that accepts exactly the string `w`. -/
def exact (w : LambekD.String Alphabet) : Grammar Alphabet := fun w' => ULift (PLift (w = w'))

/-- Canonical parse: every string `w` has a parse in `string`. -/
def mkString : ∀ (w : LambekD.String Alphabet), string w
  | [] => KleeneStar.nil [] ⟨⟨rfl⟩⟩
  | c :: cs => KleeneStar.cons (c :: cs) ⟨[c], cs, rfl⟩ ⟨c, ⟨⟨rfl⟩⟩⟩ (mkString cs)

/-- Injectivity: if `⌈w⌉` has a parse at `w'`, then `w = w'`. -/
theorem exact_injective (w w' : LambekD.String Alphabet) : exact w w' → w = w' :=
  fun ⟨⟨h⟩⟩ => h

end LambekD
