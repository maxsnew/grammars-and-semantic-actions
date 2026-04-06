import LambekD.Automata.NFA.Base
import LambekD.Grammar.RegularExpression.Base

/-!
# Thompson's construction: regex → NFA

For each regular expression constructor, defines the corresponding NFA.
The NFA accepts exactly the language of the grammar denoted by the regex.

Strong equivalence proofs (Parse NFA ≅ Grammar) are stated but deferred
(they require equalizer induction machinery not yet ported).

Ports `Thompson.Construction.*` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

-- ═══════════════════════════════════════════════════════════
-- Epsilon NFA: one accepting state, no transitions
-- ═══════════════════════════════════════════════════════════

-- def εNFA : NFA Alphabet where
--   Q := Unit
--   init := ()
--   isAcc := fun _ => true
--   Transition := Empty
--   src := Empty.elim
--   dst := Empty.elim
--   label := Empty.elim
--   ETransition := Empty
--   εSrc := Empty.elim
--   εDst := Empty.elim

-- -- Parse εNFA ≅ ε
-- -- Only `stop` is possible (Transition = ETransition = Empty).
-- def εNFA_equiv : NFA.Parse εNFA ≅g (ε : Grammar Alphabet) where
--   to := fun w trace => match trace with | .stop () _ _ eps => eps
--   from' := fun w eps => AccTrace.stop () rfl w eps
--   to_from := rfl
--   from_to := by funext w trace; exact match trace with | .stop () _ _ _ => rfl

-- -- ═══════════════════════════════════════════════════════════
-- -- Bottom NFA: one rejecting state, no transitions
-- -- ═══════════════════════════════════════════════════════════

-- def botNFA : NFA Alphabet where
--   Q := Unit
--   init := ()
--   isAcc := fun _ => false
--   Transition := Empty
--   src := Empty.elim
--   dst := Empty.elim
--   label := Empty.elim
--   ETransition := Empty
--   εSrc := Empty.elim
--   εDst := Empty.elim

-- -- Parse botNFA ≅ ⊥g
-- -- `stop` needs `true = false` (impossible), transitions are Empty.
-- def botNFA_equiv : NFA.Parse botNFA ≅g (⊥g : Grammar Alphabet) where
--   to := fun w trace => match trace with | .stop () h _ _ => nomatch h
--   from' := fun w bot => PEmpty.elim bot.down
--   to_from := by funext w bot; exact PEmpty.elim bot.down
--   from_to := by funext w trace; exact match trace with | .stop () h _ _ => nomatch h

-- -- ═══════════════════════════════════════════════════════════
-- -- Literal NFA: two states, one transition labeled c
-- -- ═══════════════════════════════════════════════════════════

-- inductive LitState where
--   | charSt | epsSt
--   deriving DecidableEq

-- def literalNFA (c : Alphabet) : NFA Alphabet where
--   Q := LitState
--   init := .charSt
--   isAcc := fun | .charSt => false | .epsSt => true
--   Transition := Unit
--   src := fun _ => .charSt
--   dst := fun _ => .epsSt
--   label := fun _ => c
--   ETransition := Empty
--   εSrc := Empty.elim
--   εDst := Empty.elim

-- -- Parse (literalNFA c) ≅ lit(c)
-- -- One `step ()` consuming c, then `stop .epsSt`.
-- def literalNFA_equiv (c : Alphabet) : NFA.Parse (literalNFA c) ≅g lit(c) where
--   to := fun w trace => match trace with
--     | .step () _ s lit (.stop LitState.epsSt _ _ eps) =>
--         ⟨⟨by rw [← s.eq, lit.down.down, eps.down.down]⟩⟩
--   from' := fun w lit => by
--     have heq := lit.down.down; subst heq
--     exact AccTrace.step () [c] ⟨[c], [], rfl⟩ ⟨⟨rfl⟩⟩
--       (AccTrace.stop LitState.epsSt rfl [] ⟨⟨rfl⟩⟩)
--   to_from := sorry
--   from_to := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Sum NFA: choice between two NFAs via ε-transitions from start
-- -- ═══════════════════════════════════════════════════════════

-- inductive SumState (N N' : NFA Alphabet) where
--   | start : SumState N N'
--   | inl : N.Q → SumState N N'
--   | inr : N'.Q → SumState N N'

-- inductive SumεTrans (N N' : NFA Alphabet) where
--   | pickL : SumεTrans N N'
--   | pickR : SumεTrans N N'
--   | nεTrans : N.ETransition → SumεTrans N N'
--   | n'εTrans : N'.ETransition → SumεTrans N N'

-- def sumNFA (N N' : NFA Alphabet) : NFA Alphabet where
--   Q := SumState N N'
--   init := .start
--   isAcc := fun
--     | .start => false
--     | .inl q => N.isAcc q
--     | .inr q' => N'.isAcc q'
--   Transition := _root_.Sum N.Transition N'.Transition
--   src := fun
--     | .inl t => .inl (N.src t)
--     | .inr t' => .inr (N'.src t')
--   dst := fun
--     | .inl t => .inl (N.dst t)
--     | .inr t' => .inr (N'.dst t')
--   label := fun
--     | .inl t => N.label t
--     | .inr t' => N'.label t'
--   ETransition := SumεTrans N N'
--   εSrc := fun
--     | .pickL => .start
--     | .pickR => .start
--     | .nεTrans t => .inl (N.εSrc t)
--     | .n'εTrans t' => .inr (N'.εSrc t')
--   εDst := fun
--     | .pickL => .inl N.init
--     | .pickR => .inr N'.init
--     | .nεTrans t => .inl (N.εDst t)
--     | .n'εTrans t' => .inr (N'.εDst t')

-- -- Parse (sumNFA N N') ≅ Parse N ⊕ Parse N'
-- def sumNFA_equiv (N N' : NFA Alphabet) : NFA.Parse (sumNFA N N') ≅g (NFA.Parse N ⊕ NFA.Parse N') where
--   to := sorry
--   from' := sorry
--   to_from := sorry
--   from_to := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Linear Product NFA: sequential composition via ε-transitions
-- -- ═══════════════════════════════════════════════════════════

-- inductive ProdεTrans (N N' : NFA Alphabet) where
--   | nAcc : (q : N.Q) → true = N.isAcc q → ProdεTrans N N'
--   | nεTrans : N.ETransition → ProdεTrans N N'
--   | n'εTrans : N'.ETransition → ProdεTrans N N'

-- def prodNFA (N N' : NFA Alphabet) : NFA Alphabet where
--   Q := _root_.Sum N.Q N'.Q
--   init := .inl N.init
--   isAcc := fun
--     | .inl _ => false
--     | .inr q' => N'.isAcc q'
--   Transition := _root_.Sum N.Transition N'.Transition
--   src := fun
--     | .inl t => .inl (N.src t)
--     | .inr t' => .inr (N'.src t')
--   dst := fun
--     | .inl t => .inl (N.dst t)
--     | .inr t' => .inr (N'.dst t')
--   label := fun
--     | .inl t => N.label t
--     | .inr t' => N'.label t'
--   ETransition := ProdεTrans N N'
--   εSrc := fun
--     | .nAcc q _ => .inl q
--     | .nεTrans t => .inl (N.εSrc t)
--     | .n'εTrans t' => .inr (N'.εSrc t')
--   εDst := fun
--     | .nAcc _ _ => .inr N'.init
--     | .nεTrans t => .inl (N.εDst t)
--     | .n'εTrans t' => .inr (N'.εDst t')

-- -- Parse (prodNFA N N') ≅ Parse N ⊗ Parse N'
-- def prodNFA_equiv (N N' : NFA Alphabet) : NFA.Parse (prodNFA N N') ≅g (NFA.Parse N ⊗ NFA.Parse N') where
--   to := sorry
--   from' := sorry
--   to_from := sorry
--   from_to := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Kleene Star NFA: iteration via ε-transitions back to start
-- -- ═══════════════════════════════════════════════════════════

-- inductive StarεTrans (N : NFA Alphabet) where
--   | enter : StarεTrans N
--   | loop : (q : N.Q) → true = N.isAcc q → StarεTrans N
--   | nεTrans : N.ETransition → StarεTrans N

-- def starNFA (N : NFA Alphabet) : NFA Alphabet where
--   Q := _root_.Sum Unit N.Q
--   init := .inl ()
--   isAcc := fun
--     | .inl _ => true
--     | .inr _ => false
--   Transition := N.Transition
--   src := fun t => .inr (N.src t)
--   dst := fun t => .inr (N.dst t)
--   label := N.label
--   ETransition := StarεTrans N
--   εSrc := fun
--     | .enter => .inl ()
--     | .loop q _ => .inr q
--     | .nεTrans t => .inr (N.εSrc t)
--   εDst := fun
--     | .enter => .inr N.init
--     | .loop _ _ => .inl ()
--     | .nεTrans t => .inr (N.εDst t)

-- -- Parse (starNFA N) ≅ (Parse N) *
-- def starNFA_equiv (N : NFA Alphabet) : NFA.Parse (starNFA N) ≅g ((NFA.Parse N) *) where
--   to := sorry
--   from' := sorry
--   to_from := sorry
--   from_to := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- regex → NFA: the overall Thompson construction
-- -- ═══════════════════════════════════════════════════════════

-- open RegularExpression in
-- def regex_to_NFA : RegularExpression Alphabet → NFA Alphabet
--   | .eps => εNFA
--   | .bot => botNFA
--   | .tensor r r' => prodNFA (regex_to_NFA r) (regex_to_NFA r')
--   | .literal c => literalNFA c
--   | .sum r r' => sumNFA (regex_to_NFA r) (regex_to_NFA r')
--   | .star r => starNFA (regex_to_NFA r)

-- end LambekD
