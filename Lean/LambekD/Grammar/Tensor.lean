import LambekD.Core.Defs
import LambekD.Elab

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C D : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- Bifunctoriality
-- ═══════════════════════════════════════════════════════════

def gtensorIntro (f : A ⊢ B) (g : C ⊢ D) : A ⊗ C ⊢ B ⊗ D :=
  fun _ ⟨s, a, c⟩ => ⟨s, f _ a, g _ c⟩

theorem gtensorIntro_comp {E F : Grammar Alphabet}
    (f : A ⊢ B) (f' : B ⊢ E) (g : C ⊢ D) (g' : D ⊢ F) :
    gtensorIntro (f' ∘g f) (g' ∘g g) = gtensorIntro f' g' ∘g gtensorIntro f g := rfl

theorem gtensorIntro_id : gtensorIntro (gId A) (gId B) = gId (A ⊗ B) := rfl

-- ═══════════════════════════════════════════════════════════
-- Right unit: A ⊗ ε ≅ A
-- ═══════════════════════════════════════════════════════════

def gεUnitR : A ⊗ ε ⊢ A :=
  fun w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩ => by
    cases nil; simp at eq; cases eq; exact a

def gεUnitRInv : A ⊢ A ⊗ ε :=
  fun w a => ⟨⟨w, [], by simp⟩, a, ⟨PLift.up rfl⟩⟩

theorem gεUnitR_inv_comp : gεUnitR ∘g gεUnitRInv = gId (A := A) := by
  funext w a; simp only [gComp, gεUnitRInv, gεUnitR, gId]

theorem gεUnitRInv_comp : gεUnitRInv ∘g gεUnitR = gId (A := A ⊗ ε) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Left unit: ε ⊗ A ≅ A
-- ═══════════════════════════════════════════════════════════

def gεUnitL : ε ⊗ A ⊢ A :=
  fun w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩ => by
    cases nil; simp at eq; cases eq; exact a

def gεUnitLInv : A ⊢ ε ⊗ A :=
  fun w a => ⟨⟨[], w, by simp⟩, ⟨PLift.up rfl⟩, a⟩

theorem gεUnitL_inv_comp : gεUnitL ∘g gεUnitLInv = gId (A := A) := by
  funext w a; simp only [gComp, gεUnitLInv, gεUnitL, gId]

theorem gεUnitLInv_comp : gεUnitLInv ∘g gεUnitL = gId (A := ε ⊗ A) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Associativity: (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
-- ═══════════════════════════════════════════════════════════

def gtensorAssoc : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C) :=
  fun _ ⟨s, ⟨s', a, b⟩, c⟩ =>
    ⟨⟨s'.left, s'.right ++ s.right,
      by rw [← List.append_assoc]; rw [s'.eq]; rw [s.eq]⟩,
     a, ⟨⟨s'.right, s.right, rfl⟩, b, c⟩⟩

def gtensorAssocInv : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C :=
  fun _ ⟨s, a, ⟨s', b, c⟩⟩ =>
    ⟨⟨s.left ++ s'.left, s'.right,
      by simp; rw [s'.eq]; rw [s.eq]⟩,
     ⟨⟨s.left, s'.left, rfl⟩, a, b⟩, c⟩

theorem gtensorAssoc_inv : gtensorAssoc ∘g gtensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨l', r', eq'⟩, b, c⟩⟩
  cases eq with | refl => cases eq' with | refl => rfl

theorem gtensorAssocInv_inv : gtensorAssocInv ∘g gtensorAssoc = gId (A := (A ⊗ B) ⊗ C) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, b⟩, c⟩
  cases eq with | refl => cases eq' with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Naturality
-- ═══════════════════════════════════════════════════════════

theorem gtensorAssoc_natural (f : A ⊢ A) (g : B ⊢ B) (h : C ⊢ C) :
    gtensorAssoc ∘g gtensorIntro (gtensorIntro f g) h =
    gtensorIntro f (gtensorIntro g h) ∘g gtensorAssoc := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, b⟩, c⟩
  cases eq with | refl => cases eq' with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Coherence: Pentagon and Triangle
-- ═══════════════════════════════════════════════════════════

theorem pentagon :
    gtensorIntro (gId A) (gtensorAssoc (A := B) (B := C) (C := D)) ∘g
    gtensorAssoc (A := A) (B := B ⊗ C) (C := D) ∘g
    gtensorIntro (gtensorAssoc (A := A) (B := B) (C := C)) (gId D) =
    gtensorAssoc (A := A) (B := B) (C := C ⊗ D) ∘g
    gtensorAssoc (A := A ⊗ B) (B := C) (C := D) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, ⟨⟨l'', r'', eq''⟩, a, b⟩, c⟩, d⟩
  cases eq with | refl => cases eq' with | refl => cases eq'' with | refl =>
    simp only [gComp, gtensorAssoc, gtensorIntro, gId]
    grind

theorem triangle :
    gtensorIntro (gId A) (gεUnitL (A := B)) ∘g
    gtensorAssoc (A := A) (B := ε) (C := B) =
    gtensorIntro (gεUnitR (A := A)) (gId B) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, ⟨⟨nil⟩⟩⟩, b⟩
  cases eq with | refl => cases nil with | refl =>
    simp at eq'; cases eq' with | refl =>
      simp only [gComp, gtensorAssoc, gtensorIntro, gId, gεUnitR, gεUnitL]
      grind

end LambekD
