import LambekD.Grammar

variable {Alphabet : Type}
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]
include Alphabet

def Tensor (A B : Grammar Alphabet) : Grammar Alphabet := sorry
