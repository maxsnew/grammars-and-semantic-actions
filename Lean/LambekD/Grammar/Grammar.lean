variable (Alphabet : Type)
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]

def SemString := List Alphabet

def Spltting (w : SemString)
|

def Grammar := SemString Alphabet → Type

def Term (A B : Grammar Alphabet) := (w : SemString Alphabet) → A w → B w

syntax term "⊢" term : term
macro_rules
| `($A:term ⊢ $B:term) => `(Term $A $B)
