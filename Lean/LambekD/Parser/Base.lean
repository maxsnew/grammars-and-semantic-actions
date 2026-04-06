import LambekD.Grammar.Properties.Base
import LambekD.Grammar.String.Base

/-!
# Parser definition

A parser for grammar `A` (with reject grammar `B`) consists of:
- A proof that `A` and `B` are disjoint
- A function `string ⊢ A ⊕ B` that classifies every string

Ports `Parser.Base` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

structure Parser (A B : Grammar Alphabet) where
  disj : Disjoint A B
  parse : string ⊢ A ⊕ B

namespace Parser

def run {A B : Grammar Alphabet} (P : Parser A B) (w : LambekD.String Alphabet) : _root_.Sum (A w) (B w) :=
  P.parse w (mkString w)

def accept? {A B : Grammar Alphabet} (P : Parser A B) (w : LambekD.String Alphabet) : Bool :=
  match P.run w with
  | .inl _ => true
  | .inr _ => false

end Parser

end LambekD
