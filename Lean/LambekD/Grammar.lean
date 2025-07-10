variable (Alphabet : Type)
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]

abbrev SemString := List Alphabet

def Grammar := SemString Alphabet → Type

structure Splitting (w : SemString Alphabet) where
  left : SemString Alphabet
  right : SemString Alphabet
  concatEq : left ++ right = w

def Reduction (A B : Grammar Alphabet) := (w : SemString Alphabet) → A w → B w

syntax term "⊢" term : term
macro_rules
| `($A:term ⊢ $B:term) => `(Reduction $A $B)
