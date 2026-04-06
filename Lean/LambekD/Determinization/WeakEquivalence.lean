import LambekD.Automata.NFA.Base
import LambekD.Automata.DFA.Base
import LambekD.Grammar.Equivalence

/-!
# Determinization: NFA → DFA via powerset construction

Given an NFA with finitely ordered states and transitions, constructs a
DFA (the powerset automaton) that accepts the same language. The DFA's states
are ε-closed decidable predicates on the NFA's state space.

Key results (with sorry for the heavy trace transformation proofs):
- `εClosed`: ε-closed subsets of NFA states
- `εClosure`: compute the ε-closure of a set of states
- `powersetDFA`: the powerset DFA construction
- `NFA_weakEquiv_DFA`: weak equivalence between NFA and powerset DFA traces

Ports `Determinization.WeakEquivalence` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

-- ═══════════════════════════════════════════════════════════
-- Decidable predicates on NFA states
-- ═══════════════════════════════════════════════════════════

/-- A decidable predicate on a type Q. -/
structure DecPred (Q : Type) where
  mem : Q → Prop
  dec : ∀ q, Decidable (mem q)

namespace DecPred

variable {Q : Type}

instance (X : DecPred Q) (q : Q) : Decidable (X.mem q) := X.dec q

def empty : DecPred Q where
  mem _ := False
  dec _ := .isFalse (by tauto)

def singleton [DecidableEq Q] (q₀ : Q) : DecPred Q where
  mem q := q = q₀
  dec q := inferInstanceAs (Decidable (q = q₀))

def union (X Y : DecPred Q) : DecPred Q where
  mem q := X.mem q ∨ Y.mem q
  dec q := inferInstanceAs (Decidable (X.mem q ∨ Y.mem q))

end DecPred

-- ═══════════════════════════════════════════════════════════
-- ε-closed predicates
-- ═══════════════════════════════════════════════════════════

/-- A predicate on NFA states is ε-closed if whenever src(t) ∈ X for an
    ε-transition t, also dst(t) ∈ X. -/
def isεClosed (nfa : NFA Alphabet) (X : DecPred nfa.Q) : Prop :=
  ∀ (t : nfa.ETransition), X.mem (nfa.εSrc t) → X.mem (nfa.εDst t)

/-- An ε-closed decidable predicate on NFA states. -/
structure εClosed (nfa : NFA Alphabet) where
  pred : DecPred nfa.Q
  closed : isεClosed nfa pred

namespace εClosed

variable {nfa : NFA Alphabet}

/-- Membership in an ε-closed set. -/
def mem (X : εClosed nfa) (q : nfa.Q) : Prop := X.pred.mem q

instance (X : εClosed nfa) (q : nfa.Q) : Decidable (X.mem q) := X.pred.dec q

end εClosed

-- ═══════════════════════════════════════════════════════════
-- ε-closure computation
-- ═══════════════════════════════════════════════════════════

/-- Compute the ε-closure of a decidable predicate.
    This adds all states reachable via ε-transitions from states in the set.
    Requires finiteness of states and ε-transitions for decidability. -/
noncomputable def εClosure (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.ETransition] (X : DecPred nfa.Q) : εClosed nfa where
  pred := sorry -- iterate: add εDst for each εSrc ∈ X until fixpoint
  closed := sorry

/-- The ε-closure contains the original set. -/
theorem εClosure_lift {nfa : NFA Alphabet} [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.ETransition] (X : DecPred nfa.Q) (q : nfa.Q) :
    X.mem q → (εClosure nfa X).mem q := sorry

-- ═══════════════════════════════════════════════════════════
-- Literal closure
-- ═══════════════════════════════════════════════════════════

/-- States reachable from X via a single transition labeled c. -/
noncomputable def litClosure (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.Transition] [DecidableEq Alphabet]
    (c : Alphabet) (X : DecPred nfa.Q) : DecPred nfa.Q where
  mem q := ∃ (t : nfa.Transition), X.mem (nfa.src t) ∧ nfa.label t = c ∧ nfa.dst t = q
  dec q := sorry -- decidable by finiteness of transitions

-- ═══════════════════════════════════════════════════════════
-- Powerset DFA construction
-- ═══════════════════════════════════════════════════════════

/-- The powerset DFA: states are ε-closed subsets of the NFA's states.
    - init: ε-closure of {NFA.init}
    - isAcc: true if any accepting NFA state is in the set
    - δ: given set X and character c, take ε-closure of literal closure -/
noncomputable def powersetDFA (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.Transition] [Fintype nfa.ETransition] [DecidableEq Alphabet] :
    DeterministicAutomaton Alphabet (εClosed nfa) where
  init := εClosure nfa (DecPred.singleton nfa.init)
  isAcc := fun X => sorry -- decide if ∃ q ∈ X, nfa.isAcc q = true
  δ := fun X c => εClosure nfa (litClosure nfa c X.pred)

-- ═══════════════════════════════════════════════════════════
-- Trace transformations (stated, proofs deferred)
-- ═══════════════════════════════════════════════════════════

-- NFA → DFA direction: an NFA accepting trace induces a DFA accepting trace
noncomputable def nfaToDfa (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.Transition] [Fintype nfa.ETransition] [DecidableEq Alphabet] :
    NFA.Parse nfa ⊢ Trace (εClosed nfa) (powersetDFA nfa) true (powersetDFA nfa).init :=
  sorry

-- DFA → NFA direction: a DFA accepting trace induces an NFA accepting trace
noncomputable def dfaToNfa (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.Transition] [Fintype nfa.ETransition] [DecidableEq Alphabet] :
    Trace (εClosed nfa) (powersetDFA nfa) true (powersetDFA nfa).init ⊢ NFA.Parse nfa :=
  sorry

-- ═══════════════════════════════════════════════════════════
-- Weak equivalence
-- ═══════════════════════════════════════════════════════════

/-- The NFA's accepting traces are weakly equivalent to the powerset DFA's
    accepting traces. This is the core correctness theorem for determinization. -/
noncomputable def NFA_weakEquiv_DFA (nfa : NFA Alphabet) [Fintype nfa.Q] [DecidableEq nfa.Q]
    [Fintype nfa.Transition] [Fintype nfa.ETransition] [DecidableEq Alphabet] :
    NFA.Parse nfa ≈g
    Trace (εClosed nfa) (powersetDFA nfa) true (powersetDFA nfa).init :=
  ⟨nfaToDfa nfa, dfaToNfa nfa⟩

end LambekD
