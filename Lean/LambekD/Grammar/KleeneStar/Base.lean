import LambekD.Elab

/-! # Kleene star as a grammar inductive type -/

namespace LambekD

open LambekD LambekD.Elab

universe uAlph

variable {Alphabet : Type uAlph}

-- The Kleene star A * is the inductive grammar with
-- nil : ε → A * (empty repetition), cons : A ⊗ A * → A * (one more)
grammar_inductive KleeneStar (A : Grammar Alphabet) : Grammar Alphabet where
  | nil : GEpsilon
  | cons : A ⊗ KleeneStar A

scoped postfix:max " * " => KleeneStar

-- Introduction: the empty string parses as A *.
def NIL (A : Grammar Alphabet) : ε ⊢ A * :=
  [| x => nil x |]

-- Introduction: A followed by A * gives A *.
def CONS (A : Grammar Alphabet) : A ⊗ A * ⊢ A * :=
  [| x => cons x |]

-- Right fold: given a nil case and a cons case, eliminate A *.
def foldStarR {A B : Grammar Alphabet}
    (nilCase : ε ⊢ B) (consCase : A ⊗ B ⊢ B) : A * ⊢ B :=
  fun w t => match w, t with
  | _, .nil _ e => nilCase _ e
  | _, .cons _ s a t' => consCase _ ⟨s, a, foldStarR nilCase consCase _ t'⟩

end LambekD
