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

def tensorIntro (f : A ⊢ B) (g : C ⊢ D) : A ⊗ C ⊢ B ⊗ D :=
  fun _ ⟨s, a, c⟩ => ⟨s, f _ a, g _ c⟩

def tensorIntro' (f : A ⊢ B) (g : C ⊢ D) : A ⊗ C ⊢ B ⊗ D :=
  [| a c => ( #[f] a , #[g] c ) |]

theorem tensorIntro_comp {E F : Grammar Alphabet}
    (f : A ⊢ B) (f' : B ⊢ E) (g : C ⊢ D) (g' : D ⊢ F) :
    tensorIntro (f' ∘g f) (g' ∘g g) = tensorIntro f' g' ∘g tensorIntro f g := rfl

theorem tensorIntro_id : tensorIntro (gId A) (gId B) = gId (A ⊗ B) := rfl

-- ═══════════════════════════════════════════════════════════
-- Right unit: A ⊗ ε ≅ A
-- ═══════════════════════════════════════════════════════════

def εUnitR : A ⊗ Epsilon ⊢ A :=
  fun w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩ => by
    cases nil; simp at eq; cases eq; exact a

def εUnitRInv : A ⊢ A ⊗ Epsilon :=
  fun w a => ⟨⟨w, [], by simp⟩, a, ⟨PLift.up rfl⟩⟩

theorem εUnitR_inv_comp : εUnitR ∘g εUnitRInv = gId (A := A) := by
  funext w a; simp only [gComp, εUnitRInv, εUnitR, gId]

theorem εUnitRInv_comp : εUnitRInv ∘g εUnitR = gId (A := A ⊗ Epsilon) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Left unit: ε ⊗ A ≅ A
-- ═══════════════════════════════════════════════════════════

def εUnitL : Epsilon ⊗ A ⊢ A :=
  fun w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩ => by
    cases nil; simp at eq; cases eq; exact a

def εUnitLInv : A ⊢ Epsilon ⊗ A :=
  fun w a => ⟨⟨[], w, by simp⟩, ⟨PLift.up rfl⟩, a⟩

theorem εUnitL_inv_comp : εUnitL ∘g εUnitLInv = gId (A := A) := by
  funext w a; simp only [gComp, εUnitLInv, εUnitL, gId]

theorem εUnitLInv_comp : εUnitLInv ∘g εUnitL = gId (A := Epsilon ⊗ A) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Associativity: (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
-- ═══════════════════════════════════════════════════════════

def tensorAssoc : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C) :=
  fun _ ⟨s, ⟨s', a, b⟩, c⟩ =>
    ⟨⟨s'.left, s'.right ++ s.right,
      by rw [← List.append_assoc]; rw [s'.eq]; rw [s.eq]⟩,
     a, ⟨⟨s'.right, s.right, rfl⟩, b, c⟩⟩

def tensorAssocInv : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C :=
  fun _ ⟨s, a, ⟨s', b, c⟩⟩ =>
    ⟨⟨s.left ++ s'.left, s'.right,
      by simp; rw [s'.eq]; rw [s.eq]⟩,
     ⟨⟨s.left, s'.left, rfl⟩, a, b⟩, c⟩

theorem tensorAssoc_inv : tensorAssoc ∘g tensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨l', r', eq'⟩, b, c⟩⟩
  cases eq with | refl => cases eq' with | refl => rfl

theorem tensorAssocInv_inv : tensorAssocInv ∘g tensorAssoc = gId (A := (A ⊗ B) ⊗ C) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, b⟩, c⟩
  cases eq with | refl => cases eq' with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Naturality
-- ═══════════════════════════════════════════════════════════

theorem tensorAssoc_natural (f : A ⊢ A) (g : B ⊢ B) (h : C ⊢ C) :
    tensorAssoc ∘g tensorIntro (tensorIntro f g) h =
    tensorIntro f (tensorIntro g h) ∘g tensorAssoc := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, b⟩, c⟩
  cases eq with | refl => cases eq' with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- Coherence: Pentagon and Triangle
-- ═══════════════════════════════════════════════════════════

theorem pentagon :
    tensorIntro (gId A) (tensorAssoc (A := B) (B := C) (C := D)) ∘g
    tensorAssoc (A := A) (B := B ⊗ C) (C := D) ∘g
    tensorIntro (tensorAssoc (A := A) (B := B) (C := C)) (gId D) =
    tensorAssoc (A := A) (B := B) (C := C ⊗ D) ∘g
    tensorAssoc (A := A ⊗ B) (B := C) (C := D) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, ⟨⟨l'', r'', eq''⟩, a, b⟩, c⟩, d⟩
  cases eq with | refl => cases eq' with | refl => cases eq'' with | refl =>
    simp only [gComp, tensorAssoc, tensorIntro, gId]
    grind

theorem triangle :
    tensorIntro (gId A) (εUnitL (A := B)) ∘g
    tensorAssoc (A := A) (B := Epsilon) (C := B) =
    tensorIntro (εUnitR (A := A)) (gId B) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨l', r', eq'⟩, a, ⟨⟨nil⟩⟩⟩, b⟩
  cases eq with | refl => cases nil with | refl =>
    simp at eq'; cases eq' with | refl =>
      simp only [gComp, tensorAssoc, tensorIntro, gId, εUnitR, εUnitL]
      grind

end LambekD
