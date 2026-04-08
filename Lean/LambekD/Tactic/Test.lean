import LambekD.Tactic.Simp

/-!
# Tests for grammar proof tactics

Verifies that `splitting_cases`, `grammar_ext`, and `simp [grammar_simp]`
work on the proof patterns from the grammar theory modules.
-/

namespace LambekD.Tactic.Test

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}
variable {A B C D : Grammar Alphabet}

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: tensor associativity round-trips
-- Previously 2 lines each, now 1 line
-- ═══════════════════════════════════════════════════════════

example : gtensorAssoc ∘g gtensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by grammar_ext
example : gtensorAssocInv ∘g gtensorAssoc = gId (A := (A ⊗ B) ⊗ C) := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: naturality
-- ═══════════════════════════════════════════════════════════

example (f : A ⊢ A) (g : B ⊢ B) (h : C ⊢ C) :
    gtensorAssoc ∘g gtensorIntro (gtensorIntro f g) h =
    gtensorIntro f (gtensorIntro g h) ∘g gtensorAssoc := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: ε unit (simple direction)
-- ═══════════════════════════════════════════════════════════

-- Was: funext w a; simp only [gComp, gεUnitRInv, gεUnitR, gId]
example : gεUnitR ∘g gεUnitRInv = gId (A := A) := by grammar_ext
example : gεUnitL ∘g gεUnitLInv = gId (A := A) := by grammar_ext

-- ε unit inverse round-trips need simp normalization of l ++ [] = w
-- before subst. grammar_ext handles the destructuring, leaving a
-- goal that simp_all can close.
-- Was: funext w ⟨⟨l, r, eq⟩, a, ⟨nil⟩⟩
--      cases nil with | refl => simp at eq; cases eq with | refl => rfl
example : gεUnitRInv ∘g gεUnitR = gId (A := A ⊗ GEpsilon) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

example : gεUnitLInv ∘g gεUnitL = gId (A := GEpsilon ⊗ A) := by
  funext w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩
  cases nil with | refl => simp at eq; cases eq with | refl => rfl

-- ═══════════════════════════════════════════════════════════
-- grammar_ext: linear function β laws
-- Previously: funext w ⟨⟨l, r, eq⟩, a, b⟩; cases eq with | refl => rfl
-- ═══════════════════════════════════════════════════════════

example (f : A ⊗ B ⊢ C) :
    glimpRApp ∘g gtensorIntro (glimpRIntro f) (gId B) = f := by grammar_ext

example (f : A ⊗ B ⊢ C) :
    glimpLApp ∘g gtensorIntro (gId A) (glimpLIntro f) = f := by grammar_ext

-- ═══════════════════════════════════════════════════════════
-- splitting_cases standalone
-- ═══════════════════════════════════════════════════════════

-- With named variables
example : gtensorAssoc ∘g gtensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext w ⟨⟨l, r, eq⟩, a, ⟨⟨l', r', eq'⟩, b, c⟩⟩; splitting_cases

-- With anonymous variables
example : gtensorAssoc ∘g gtensorAssocInv = gId (A := A ⊗ (B ⊗ C)) := by
  funext _ ⟨⟨_, _, _⟩, _, ⟨⟨_, _, _⟩, _, _⟩⟩; splitting_cases

-- ═══════════════════════════════════════════════════════════
-- grammar_simp: composition laws
-- ═══════════════════════════════════════════════════════════

example {E : Grammar Alphabet} (f : C ⊢ D) (g : B ⊢ C) (h : A ⊢ B) :
    f ∘g (g ∘g h) = (f ∘g g) ∘g h := by simp only [grammar_simp]

example (f : A ⊢ B) : gId B ∘g f = f := by simp only [grammar_simp]
example (f : A ⊢ B) : f ∘g gId A = f := by simp only [grammar_simp]

-- ═══════════════════════════════════════════════════════════
-- grammar_simp: connective laws
-- ═══════════════════════════════════════════════════════════

example : gtensorIntro (gId A) (gId B) = gId (A ⊗ B) := by simp only [grammar_simp]

example (f : C ⊢ A) (g : C ⊢ B) : gprodProj₁ ∘g gprodIntro f g = f := by
  simp only [grammar_simp]
example (f : C ⊢ A) (g : C ⊢ B) : gprodProj₂ ∘g gprodIntro f g = g := by
  simp only [grammar_simp]

example (f : A ⊢ C) (g : B ⊢ C) : gsumElim f g ∘g gsumInl = f := by
  simp only [grammar_simp]
example (f : A ⊢ C) (g : B ⊢ C) : gsumElim f g ∘g gsumInr = g := by
  simp only [grammar_simp]

-- ═══════════════════════════════════════════════════════════
-- StrongEquiv via grammar_ext
-- ═══════════════════════════════════════════════════════════

def gtensorAssocEquiv : (A ⊗ B) ⊗ C ≅g A ⊗ (B ⊗ C) where
  to := gtensorAssoc
  from' := gtensorAssocInv
  to_from := by grammar_ext
  from_to := by grammar_ext

end LambekD.Tactic.Test
