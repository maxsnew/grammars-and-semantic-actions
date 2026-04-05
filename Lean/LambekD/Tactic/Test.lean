import LambekD.Tactic.Simp

/-!
# Tests for grammar proof tactics

Verifies that `splitting_cases`, `grammar_ext`, and `simp [grammar_simp]`
work on the proof patterns from the grammar theory modules.
-/

namespace LambekD.Tactic.Test

open LambekD

variable [AlphabetStr]
variable {A B C D : Grammar}

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: tensor associativity round-trips
-- Previously 2 lines each, now 1 line
-- ═══════════════════════════════════════════════════════════

example : tensorAssoc ∘g tensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by grammar_ext
example : tensorAssocInv ∘g tensorAssoc = gId (A := (A ⊗ B) ⊗ C) := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: naturality
-- ═══════════════════════════════════════════════════════════

example (f : A ⊢ A) (g : B ⊢ B) (h : C ⊢ C) :
    tensorAssoc ∘g tensorIntro (tensorIntro f g) h =
    tensorIntro f (tensorIntro g h) ∘g tensorAssoc := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: ε unit (simple direction)
-- ═══════════════════════════════════════════════════════════

-- Was: funext w a; simp only [gComp, εUnitRInv, εUnitR, gId]
example : εUnitR ∘g εUnitRInv = gId (A := A) := by grammar_ext
example : εUnitL ∘g εUnitLInv = gId (A := A) := by grammar_ext

-- ε unit inverse round-trips need simp normalization of l ++ [] = w
-- before subst. grammar_ext handles the destructuring, leaving a
-- goal that simp_all can close.
-- Was: funext w ⟨⟨l, r, eq⟩, a, ⟨nil⟩⟩
--      cases nil with | refl => simp at eq; cases eq with | refl => rfl
example : εUnitRInv ∘g εUnitR = gId (A := A ⊗ Epsilon) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨nil⟩⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

example : εUnitLInv ∘g εUnitL = gId (A := Epsilon ⊗ A) := by
  funext w ⟨⟨l, r, eq⟩, ⟨nil⟩, a⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: linear function β laws
-- Previously: funext w ⟨⟨l, r, eq⟩, a, b⟩; cases eq with | refl => rfl
-- ═══════════════════════════════════════════════════════════

example (f : A ⊗ B ⊢ C) :
    limpRApp ∘g tensorIntro (gId A) (limpRIntro f) = f := by grammar_ext

example (f : A ⊗ B ⊢ C) :
    limpLApp ∘g tensorIntro (limpLIntro f) (gId B) = f := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- splitting_cases standalone
-- ═══════════════════════════════════════════════════════════

-- With named variables
example : tensorAssoc ∘g tensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨l', r', eq'⟩, b, c⟩⟩; splitting_cases

-- With anonymous variables
example : tensorAssoc ∘g tensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext _ ⟨⟨_, _, _⟩, _, ⟨⟨_, _, _⟩, _, _⟩⟩; splitting_cases

-- ═══════════════════════════════════════════════════════════
-- grammar_simp: composition laws
-- ═══════════════════════════════════════════════════════════

example {E : Grammar} (f : C ⊢ D) (g : B ⊢ C) (h : A ⊢ B) :
    f ∘g (g ∘g h) = (f ∘g g) ∘g h := by simp only [grammar_simp]

example (f : A ⊢ B) : gId B ∘g f = f := by simp only [grammar_simp]
example (f : A ⊢ B) : f ∘g gId A = f := by simp only [grammar_simp]

-- ═══════════════════════════════════════════════════════════
-- grammar_simp: connective laws
-- ═══════════════════════════════════════════════════════════

example : tensorIntro (gId A) (gId B) = gId (A ⊗ B) := by simp only [grammar_simp]

example (f : C ⊢ A) (g : C ⊢ B) : prodProj₁ ∘g prodIntro f g = f := by
  simp only [grammar_simp]
example (f : C ⊢ A) (g : C ⊢ B) : prodProj₂ ∘g prodIntro f g = g := by
  simp only [grammar_simp]

example (f : A ⊢ C) (g : B ⊢ C) : sumElim f g ∘g sumInl = f := by
  simp only [grammar_simp]
example (f : A ⊢ C) (g : B ⊢ C) : sumElim f g ∘g sumInr = g := by
  simp only [grammar_simp]

-- ═══════════════════════════════════════════════════════════
-- StrongEquiv via grammar_ext
-- ═══════════════════════════════════════════════════════════

def tensorAssocEquiv : (A ⊗ B) ⊗ C ≅g A ⊗ (B ⊗ C) where
  to := tensorAssoc
  from' := tensorAssocInv
  to_from := by grammar_ext
  from_to := by grammar_ext

end LambekD.Tactic.Test
