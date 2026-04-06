import LambekD.Core.Connectives
import LambekD.Grammar.KleeneStar.Base

/-!
# Regular expressions

Syntax type for regular expressions and interpretation into grammars.

Ports `Grammar.RegularExpression.Base` from the Agda formalization.
-/

namespace LambekD

open LambekD


inductive RegularExpression.{uAlph} (Alphabet : Type uAlph) where
  | eps : RegularExpression Alphabet
  | bot : RegularExpression Alphabet
  | tensor : RegularExpression Alphabet → RegularExpression Alphabet → RegularExpression Alphabet
  | literal : Alphabet → RegularExpression Alphabet
  | sum : RegularExpression Alphabet → RegularExpression Alphabet → RegularExpression Alphabet
  | star : RegularExpression Alphabet → RegularExpression Alphabet

namespace RegularExpression

scoped infixr:20 " ⊗r " => tensor
scoped infixr:20 " ⊕r " => sum
scoped postfix:30 " *r" => star

universe uAlph

variable {Alphabet : Type uAlph}

def toGrammar.{u} : RegularExpression.{uAlph} Alphabet → Grammar.{max u uAlph, uAlph} Alphabet
  | .eps => Epsilon
  | .bot => Bottom
  | .tensor r r' => Tensor r.toGrammar r'.toGrammar
  | .literal c => Literal c
  | .sum r r' => Sum r.toGrammar r'.toGrammar
  | .star r => KleeneStar r.toGrammar

scoped notation "⟦" r "⟧r" => toGrammar r

def plus (r : RegularExpression Alphabet) : RegularExpression Alphabet := r.tensor r.star

end RegularExpression

end LambekD
