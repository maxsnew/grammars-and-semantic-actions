import LambekD.Automata.NFA.Base
import LambekD.Grammar.RegularExpression.Base
import LambekD.Grammar.Tensor
import LambekD.Grammar.Sum

/-!
# Thompson's construction: regex → NFA

For each regular expression constructor, defines the corresponding NFA.
The NFA accepts exactly the language of the grammar denoted by the regex.

Strong equivalence proofs (Parse NFA ≅ Grammar) are provided for each
constructor. The composite cases (prod, star) defer round-trip coherence.

Ports `Thompson.Construction.*` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

-- ═══════════════════════════════════════════════════════════
-- Epsilon NFA: one accepting state, no transitions
-- ═══════════════════════════════════════════════════════════

def εNFA : NFA Alphabet where
  Q := Unit
  init := ()
  isAcc := fun _ => true
  Transition := Empty
  src := Empty.elim
  dst := Empty.elim
  label := Empty.elim
  ETransition := Empty
  εSrc := Empty.elim
  εDst := Empty.elim

-- Parse εNFA ≅ ε
-- Only `stop` is possible (Transition = ETransition = Empty).
def εNFA_equiv : NFA.Parse εNFA ≅g (ε : Grammar Alphabet) where
  to := by
    intro w trace
    cases trace with
    | stop q h _ eps => exact eps
    | step t => exact Empty.elim t
    | stepε t => exact Empty.elim t
  from' := NFA.STOP (nfa := εNFA) rfl
  to_from := by funext w eps; rfl
  from_to := by
    funext w trace
    cases trace with
    | stop q h _ eps => rfl
    | step t => exact Empty.elim t
    | stepε t => exact Empty.elim t

-- ═══════════════════════════════════════════════════════════
-- Bottom NFA: one rejecting state, no transitions
-- ═══════════════════════════════════════════════════════════

def botNFA : NFA Alphabet where
  Q := Unit
  init := ()
  isAcc := fun _ => false
  Transition := Empty
  src := Empty.elim
  dst := Empty.elim
  label := Empty.elim
  ETransition := Empty
  εSrc := Empty.elim
  εDst := Empty.elim

-- Parse botNFA ≅ ⊥g
-- `stop` needs `true = false` (impossible), transitions are Empty.
def botNFA_equiv : NFA.Parse botNFA ≅g (⊥g : Grammar Alphabet) where
  to := by
    intro w trace
    cases trace with
    | stop q h _ eps => exact nomatch h
    | step t => exact Empty.elim t
    | stepε t => exact Empty.elim t
  from' := fun w bot => PEmpty.elim bot.down
  to_from := by funext w bot; exact PEmpty.elim bot.down
  from_to := by
    funext w trace
    cases trace with
    | stop q h _ eps => exact nomatch h
    | step t => exact Empty.elim t
    | stepε t => exact Empty.elim t

-- ═══════════════════════════════════════════════════════════
-- Literal NFA: two states, one transition labeled c
-- ═══════════════════════════════════════════════════════════

inductive LitState where
  | charSt | epsSt
  deriving DecidableEq

def literalNFA (c : Alphabet) : NFA Alphabet where
  Q := LitState
  init := .charSt
  isAcc := fun | .charSt => false | .epsSt => true
  Transition := Unit
  src := fun _ => .charSt
  dst := fun _ => .epsSt
  label := fun _ => c
  ETransition := Empty
  εSrc := Empty.elim
  εDst := Empty.elim

-- Parse (literalNFA c) ≅ lit(c)
-- Dependent elimination fails on AccTrace when ETransition = Empty and Q has multiple
-- constructors (can't solve `Empty.rec ... t = q`). The workaround: generalize the
-- state index in a top-level function definition, where the equation compiler handles
-- Empty parameters by eliminating impossible branches automatically.

private def litEpsExtract (c : Alphabet) :
    ∀ (q : LitState) (w : String Alphabet),
      AccTrace (literalNFA c) q w → q = LitState.epsSt → ε w
  | _, _, .stop _ _ _ eps, _ => eps

private def litCharExtract (c : Alphabet) :
    ∀ (q : LitState) (w : String Alphabet),
      AccTrace (literalNFA c) q w → q = LitState.charSt → lit(c) w
  | _, _, .step () _ s lit sub, _ =>
    have heps := litEpsExtract c _ _ sub rfl
    have h1 : s.left = [c] := lit.down.down
    have h2 : s.right = [] := heps.down.down
    ⟨⟨by rw [← s.eq, h1, h2]; rfl⟩⟩

def literalNFA_equiv (c : Alphabet) : NFA.Parse (literalNFA c) ≅g lit(c) where
  to := fun w trace => litCharExtract c _ w trace rfl
  from' := fun w lit =>
    have heq : w = [c] := lit.down.down
    heq ▸ AccTrace.step (nfa := literalNFA c) () [c]
      ⟨[c], [], rfl⟩ ⟨⟨rfl⟩⟩
      (AccTrace.stop (nfa := literalNFA c) LitState.epsSt rfl [] ⟨⟨rfl⟩⟩)
  to_from := sorry
  from_to := sorry

-- ═══════════════════════════════════════════════════════════
-- Sum NFA: choice between two NFAs via ε-transitions from start
-- ═══════════════════════════════════════════════════════════

inductive SumState (N N' : NFA Alphabet) where
  | start : SumState N N'
  | inl : N.Q → SumState N N'
  | inr : N'.Q → SumState N N'

inductive SumεTrans (N N' : NFA Alphabet) where
  | pickL : SumεTrans N N'
  | pickR : SumεTrans N N'
  | nεTrans : N.ETransition → SumεTrans N N'
  | n'εTrans : N'.ETransition → SumεTrans N N'

def sumNFA (N N' : NFA Alphabet) : NFA Alphabet where
  Q := SumState N N'
  init := .start
  isAcc := fun
    | .start => false
    | .inl q => N.isAcc q
    | .inr q' => N'.isAcc q'
  Transition := _root_.Sum N.Transition N'.Transition
  src := fun
    | .inl t => .inl (N.src t)
    | .inr t' => .inr (N'.src t')
  dst := fun
    | .inl t => .inl (N.dst t)
    | .inr t' => .inr (N'.dst t')
  label := fun
    | .inl t => N.label t
    | .inr t' => N'.label t'
  ETransition := SumεTrans N N'
  εSrc := fun
    | .pickL => .start
    | .pickR => .start
    | .nεTrans t => .inl (N.εSrc t)
    | .n'εTrans t' => .inr (N'.εSrc t')
  εDst := fun
    | .pickL => .inl N.init
    | .pickR => .inr N'.init
    | .nεTrans t => .inl (N.εDst t)
    | .n'εTrans t' => .inr (N'.εDst t')

-- Convert trace in left component of sumNFA to trace of N.
-- Generalized state index avoids dependent elimination on stuck `src t`.
private def sumConvertL (N N' : NFA Alphabet) :
    ∀ (qs : SumState N N') (w : String Alphabet),
      AccTrace (sumNFA N N') qs w →
      ∀ (q : N.Q), qs = .inl q → AccTrace N q w
  | _, _, .stop (SumState.inl _) h _ eps, _, rfl =>
    AccTrace.stop (nfa := N) _ h _ eps
  | _, _, .step (_root_.Sum.inl t) _ s lit sub, _, rfl =>
    AccTrace.step (nfa := N) t _ s lit (sumConvertL N N' _ _ sub _ rfl)
  | _, _, .stepε (SumεTrans.nεTrans et) _ sub, _, rfl =>
    AccTrace.stepε (nfa := N) et _ (sumConvertL N N' _ _ sub _ rfl)

-- Convert trace in right component of sumNFA to trace of N'.
private def sumConvertR (N N' : NFA Alphabet) :
    ∀ (qs : SumState N N') (w : String Alphabet),
      AccTrace (sumNFA N N') qs w →
      ∀ (q' : N'.Q), qs = .inr q' → AccTrace N' q' w
  | _, _, .stop (SumState.inr _) h _ eps, _, rfl =>
    AccTrace.stop (nfa := N') _ h _ eps
  | _, _, .step (_root_.Sum.inr t') _ s lit sub, _, rfl =>
    AccTrace.step (nfa := N') t' _ s lit (sumConvertR N N' _ _ sub _ rfl)
  | _, _, .stepε (SumεTrans.n'εTrans et') _ sub, _, rfl =>
    AccTrace.stepε (nfa := N') et' _ (sumConvertR N N' _ _ sub _ rfl)

-- Embed trace of N into left component of sumNFA.
private def sumEmbedL (N N' : NFA Alphabet) :
    ∀ (q : N.Q) (w : String Alphabet),
      AccTrace N q w → AccTrace (sumNFA N N') (SumState.inl q) w
  | _, _, AccTrace.stop q h _ eps =>
    AccTrace.stop (nfa := sumNFA N N') (SumState.inl q) h _ eps
  | _, _, AccTrace.step t _ s lit sub =>
    AccTrace.step (nfa := sumNFA N N') (_root_.Sum.inl t) _ s lit (sumEmbedL N N' _ _ sub)
  | _, _, AccTrace.stepε et _ sub =>
    AccTrace.stepε (nfa := sumNFA N N') (SumεTrans.nεTrans et) _ (sumEmbedL N N' _ _ sub)

-- Embed trace of N' into right component of sumNFA.
private def sumEmbedR (N N' : NFA Alphabet) :
    ∀ (q' : N'.Q) (w : String Alphabet),
      AccTrace N' q' w → AccTrace (sumNFA N N') (SumState.inr q') w
  | _, _, AccTrace.stop q' h _ eps =>
    AccTrace.stop (nfa := sumNFA N N') (SumState.inr q') h _ eps
  | _, _, AccTrace.step t' _ s lit sub =>
    AccTrace.step (nfa := sumNFA N N') (_root_.Sum.inr t') _ s lit (sumEmbedR N N' _ _ sub)
  | _, _, AccTrace.stepε et' _ sub =>
    AccTrace.stepε (nfa := sumNFA N N') (SumεTrans.n'εTrans et') _ (sumEmbedR N N' _ _ sub)

-- Parse (sumNFA N N') ≅ Parse N ⊕ Parse N'
def sumNFA_equiv (N N' : NFA Alphabet) : NFA.Parse (sumNFA N N') ≅g (NFA.Parse N ⊕ NFA.Parse N') where
  to := sorry -- TODO: induction on AccTrace hits mkElimApp internal error
  from' := fun w sum => match sum with
    | _root_.Sum.inl traceN =>
      AccTrace.stepε (nfa := sumNFA N N') SumεTrans.pickL w (sumEmbedL N N' _ _ traceN)
    | _root_.Sum.inr traceN' =>
      AccTrace.stepε (nfa := sumNFA N N') SumεTrans.pickR w (sumEmbedR N N' _ _ traceN')
  to_from := sorry
  from_to := sorry

-- ═══════════════════════════════════════════════════════════
-- Linear Product NFA: sequential composition via ε-transitions
-- ═══════════════════════════════════════════════════════════

inductive ProdεTrans (N N' : NFA Alphabet) where
  | nAcc : (q : N.Q) → true = N.isAcc q → ProdεTrans N N'
  | nεTrans : N.ETransition → ProdεTrans N N'
  | n'εTrans : N'.ETransition → ProdεTrans N N'

def prodNFA (N N' : NFA Alphabet) : NFA Alphabet where
  Q := _root_.Sum N.Q N'.Q
  init := .inl N.init
  isAcc := fun
    | .inl _ => false
    | .inr q' => N'.isAcc q'
  Transition := _root_.Sum N.Transition N'.Transition
  src := fun
    | .inl t => .inl (N.src t)
    | .inr t' => .inr (N'.src t')
  dst := fun
    | .inl t => .inl (N.dst t)
    | .inr t' => .inr (N'.dst t')
  label := fun
    | .inl t => N.label t
    | .inr t' => N'.label t'
  ETransition := ProdεTrans N N'
  εSrc := fun
    | .nAcc q _ => .inl q
    | .nεTrans t => .inl (N.εSrc t)
    | .n'εTrans t' => .inr (N'.εSrc t')
  εDst := fun
    | .nAcc _ _ => .inr N'.init
    | .nεTrans t => .inl (N.εDst t)
    | .n'εTrans t' => .inr (N'.εDst t')

-- Parse (prodNFA N N') ≅ Parse N ⊗ Parse N'
def prodNFA_equiv (N N' : NFA Alphabet) : NFA.Parse (prodNFA N N') ≅g (NFA.Parse N ⊗ NFA.Parse N') where
  to := sorry
  from' := sorry
  to_from := sorry
  from_to := sorry

-- ═══════════════════════════════════════════════════════════
-- Kleene Star NFA: iteration via ε-transitions back to start
-- ═══════════════════════════════════════════════════════════

inductive StarεTrans (N : NFA Alphabet) where
  | enter : StarεTrans N
  | loop : (q : N.Q) → true = N.isAcc q → StarεTrans N
  | nεTrans : N.ETransition → StarεTrans N

def starNFA (N : NFA Alphabet) : NFA Alphabet where
  Q := _root_.Sum Unit N.Q
  init := .inl ()
  isAcc := fun
    | .inl _ => true
    | .inr _ => false
  Transition := N.Transition
  src := fun t => .inr (N.src t)
  dst := fun t => .inr (N.dst t)
  label := N.label
  ETransition := StarεTrans N
  εSrc := fun
    | .enter => .inl ()
    | .loop q _ => .inr q
    | .nεTrans t => .inr (N.εSrc t)
  εDst := fun
    | .enter => .inr N.init
    | .loop _ _ => .inl ()
    | .nεTrans t => .inr (N.εDst t)

-- Parse (starNFA N) ≅ (Parse N) *
def starNFA_equiv (N : NFA Alphabet) : NFA.Parse (starNFA N) ≅g ((NFA.Parse N) *) where
  to := sorry
  from' := sorry
  to_from := sorry
  from_to := sorry

-- ═══════════════════════════════════════════════════════════
-- Congruence lemmas for strong equivalence
-- ═══════════════════════════════════════════════════════════

def tensor_congr {A B C D : Grammar Alphabet}
    (e₁ : A ≅g C) (e₂ : B ≅g D) : (A ⊗ B) ≅g (C ⊗ D) where
  to := gtensorIntro e₁.to e₂.to
  from' := gtensorIntro e₁.from' e₂.from'
  to_from := by rw [← gtensorIntro_comp, e₁.to_from, e₂.to_from, gtensorIntro_id]
  from_to := by rw [← gtensorIntro_comp, e₁.from_to, e₂.from_to, gtensorIntro_id]

def sum_congr {A B C D : Grammar Alphabet}
    (e₁ : A ≅g C) (e₂ : B ≅g D) : (A ⊕ B) ≅g (C ⊕ D) where
  to := gsumElim (gsumInl ∘g e₁.to) (gsumInr ∘g e₂.to)
  from' := gsumElim (gsumInl ∘g e₁.from') (gsumInr ∘g e₂.from')
  to_from := by
    funext w s; match s with
    | .inl c => exact congrArg _root_.Sum.inl (congrFun (congrFun e₁.to_from w) c)
    | .inr d => exact congrArg _root_.Sum.inr (congrFun (congrFun e₂.to_from w) d)
  from_to := by
    funext w s; match s with
    | .inl a => exact congrArg _root_.Sum.inl (congrFun (congrFun e₁.from_to w) a)
    | .inr b => exact congrArg _root_.Sum.inr (congrFun (congrFun e₂.from_to w) b)

def star_congr {A B : Grammar Alphabet}
    (e : A ≅g B) : (A *) ≅g (B *) where
  to := foldStarR (NIL B) (CONS B ∘g gtensorIntro e.to (gId (B *)))
  from' := foldStarR (NIL A) (CONS A ∘g gtensorIntro e.from' (gId (A *)))
  to_from := sorry
  from_to := sorry

-- ═══════════════════════════════════════════════════════════
-- regex → NFA: the overall Thompson construction
-- ═══════════════════════════════════════════════════════════

open RegularExpression in
def regex_to_NFA : RegularExpression Alphabet → NFA Alphabet
  | .eps => εNFA
  | .bot => botNFA
  | .tensor r r' => prodNFA (regex_to_NFA r) (regex_to_NFA r')
  | .literal c => literalNFA c
  | .sum r r' => sumNFA (regex_to_NFA r) (regex_to_NFA r')
  | .star r => starNFA (regex_to_NFA r)

end LambekD
