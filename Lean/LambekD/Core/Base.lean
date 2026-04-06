/-!
# Core type definitions for Lambek^D

The fundamental types: alphabet, string, grammar, and splitting.
These have no metaprogramming dependencies.
-/

namespace LambekD

abbrev String.{uAlph} (Alphabet : Type uAlph) := List Alphabet

abbrev Grammar.{uGram,uAlph} (Alphabet : Type uAlph) := String Alphabet → Type uGram

universe uAlph
variable {Alphabet : Type uAlph}

structure Splitting (w : String Alphabet) where
  left : String Alphabet
  right : String Alphabet
  eq : left ++ right = w

@[reducible] def splitting (l r : String Alphabet) : Splitting (l ++ r) := ⟨l, r, rfl⟩

@[simp] theorem Splitting.length_eq {w : String Alphabet} (s : Splitting w) :
    s.left.length + s.right.length = w.length := by
  simp [← s.eq, List.length_append]

end LambekD
