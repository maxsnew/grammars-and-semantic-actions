import LambekD.Elab

/-! # Test: new-style grammar_inductive with ↑(gcBody) -/

namespace LambekD

open LambekD LambekD.Elab

universe uAlph

variable {Alphabet : Type uAlph}

-- Test 1: KleeneStar with new ↑ syntax (no indices)
grammar_inductive KleeneStarNew (A : Grammar Alphabet) : Grammar Alphabet where
  | nil : ↑(KleeneStarNew A)
  | cons : ↑(A ⊸ KleeneStarNew A ⊸ KleeneStarNew A)

-- Verify the constructors have the expected types
#check @KleeneStarNew.nil
#check @KleeneStarNew.cons
#check @KleeneStarNew.rec

-- Test 2: Indexed grammar inductive (Trace-like)
structure SimpleAutomaton (Alphabet : Type uAlph) (Q : Type) where
  δ : Q → Alphabet → Q
  isAcc : Q → Bool

grammar_inductive Trace (Q : Type) (da : SimpleAutomaton Alphabet Q) (b : Bool) : Q → Grammar Alphabet where
  | stop : ↑(&[ q ∈ Q ] Trace Q da b q)
  | step : ↑(&[ q ∈ Q ] &[ c ∈ Alphabet ] lit(c) ⊸ Trace Q da b (da.δ q c) ⊸ Trace Q da b q)

#check @Trace.stop
#check @Trace.step
#check @Trace.rec

end LambekD
