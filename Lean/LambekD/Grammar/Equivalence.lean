import LambekD.Defs

namespace LambekD

open LambekD

variable [AlphabetStr]

-- ═══════════════════════════════════════════════════════════
-- Weak equivalence: parse transformers in both directions
-- ═══════════════════════════════════════════════════════════

structure WeakEquiv (A B : Grammar) where
  to : A ⊢ B
  from' : B ⊢ A

scoped infixl:25 " ≈g " => WeakEquiv

def WeakEquiv.refl (A : Grammar) : A ≈g A :=
  ⟨gId A, gId A⟩

def WeakEquiv.symm {A B : Grammar} (e : A ≈g B) : B ≈g A :=
  ⟨e.from', e.to⟩

def WeakEquiv.trans {A B C : Grammar} (e₁ : A ≈g B) (e₂ : B ≈g C) : A ≈g C :=
  ⟨e₂.to ∘g e₁.to, e₁.from' ∘g e₂.from'⟩

-- ═══════════════════════════════════════════════════════════
-- Strong equivalence: round-trips are identity
-- ═══════════════════════════════════════════════════════════

structure StrongEquiv (A B : Grammar) where
  to : A ⊢ B
  from' : B ⊢ A
  to_from : to ∘g from' = gId B
  from_to : from' ∘g to = gId A

scoped infixl:25 " ≅g " => StrongEquiv

def StrongEquiv.refl (A : Grammar) : A ≅g A :=
  ⟨gId A, gId A, rfl, rfl⟩

def StrongEquiv.symm {A B : Grammar} (e : A ≅g B) : B ≅g A :=
  ⟨e.from', e.to, e.from_to, e.to_from⟩

def StrongEquiv.trans {A B C : Grammar} (e₁ : A ≅g B) (e₂ : B ≅g C) : A ≅g C :=
  ⟨e₂.to ∘g e₁.to, e₁.from' ∘g e₂.from',
   by -- (e₂.to ∘g e₁.to) ∘g (e₁.from' ∘g e₂.from') = gId C
      -- definitionally: e₂.to ∘g (e₁.to ∘g e₁.from') ∘g e₂.from' = gId C
      show e₂.to ∘g (e₁.to ∘g e₁.from') ∘g e₂.from' = gId C
      rw [e₁.to_from]; exact e₂.to_from,
   by show e₁.from' ∘g (e₂.from' ∘g e₂.to) ∘g e₁.to = gId A
      rw [e₂.from_to]; exact e₁.from_to⟩

def StrongEquiv.toWeakEquiv {A B : Grammar} (e : A ≅g B) : A ≈g B :=
  ⟨e.to, e.from'⟩

end LambekD
