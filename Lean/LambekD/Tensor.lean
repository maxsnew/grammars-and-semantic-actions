import LambekD.Grammar

variable {Alphabet : Type}
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]
include Alphabet

def Tensor (A B : Grammar Alphabet) : Grammar Alphabet :=
  λ (w : SemString Alphabet) => Σ (s : Splitting Alphabet w) , A (s.left) × B (s.right)

syntax term "⊗" term : term
macro_rules
| `($A:term ⊗ $B:term) => `(Tensor $A $B)

def TensorIn {A B C D : Grammar Alphabet} : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
