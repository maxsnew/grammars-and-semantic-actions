section
  variable (Alphabet : Type)
  variable [Inhabited Alphabet]
  variable [DecidableEq Alphabet]

  namespace Grammar

  abbrev SemString := List Alphabet

  def Grammar := SemString Alphabet → Type

  -- TODO I can't figure out how to globally bind everything to the samee Alphabet,
  -- so I have to thread an Alphabet parameter through everything which is annoying
  structure Splitting (w : SemString Alphabet) where
    left : SemString Alphabet
    right : SemString Alphabet
    concatEq : left ++ right = w

  def Reduction (A B : Grammar Alphabet) := (w : SemString Alphabet) → A w → B w

  syntax term "⊢" term : term
  macro_rules
  | `($A:term ⊢ $B:term) => `(Reduction $A $B)
  end Grammar
end
