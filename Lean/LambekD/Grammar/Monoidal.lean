import LambekD.Grammar.Cat
import LambekD.Grammar.Tensor
import LambekD.Tactic

import Mathlib.CategoryTheory.Monoidal.Category

/-! # Monoidal category instance for Grammar

The tensor product `⊗` and unit `ε` equip `Grammar` with a monoidal
category structure. Coherence (pentagon, triangle, naturality) reuses the
algebraic laws proved in `Grammar.Tensor`.

Note: `uAlph = uGram` is required so that `Tensor A B` (which includes a `Splitting`
containing strings in `Type uAlph`) lands in `Grammar`. Both are parameterized
by a single universe `u`.
-/

namespace LambekD

universe u

open CategoryTheory MonoidalCategory
variable {Alphabet : Type u}

instance : MonoidalCategory (Grammar.{u, u} Alphabet) where
  tensorObj := Tensor
  whiskerLeft X _ _ f := tensorIntro (gId X) f
  whiskerRight f Z := tensorIntro f (gId Z)
  tensorUnit := ε
  associator A B C := {
    hom := tensorAssoc
    inv := tensorAssocInv
    hom_inv_id := tensorAssocInv_inv
    inv_hom_id := tensorAssoc_inv
  }
  associator_naturality {_ _ _ _ _ _} _ _ _ := by grammar_ext
  leftUnitor A := {
    hom := εUnitL.{u, u, u}
    inv := εUnitLInv.{u, u, u}
    hom_inv_id := εUnitLInv_comp.{u, u, u}
    inv_hom_id := εUnitL_inv_comp.{u, u, u}
  }
  leftUnitor_naturality _ := by
    funext w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩
    cases nil with | refl => cases eq with | refl => rfl
  rightUnitor A := {
    hom := εUnitR.{u, u, u}
    inv := εUnitRInv.{u, u, u}
    hom_inv_id := εUnitRInv_comp.{u, u, u}
    inv_hom_id := εUnitR_inv_comp.{u, u, u}
  }
  rightUnitor_naturality _ := by
    funext w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩
    cases nil with | refl => simp at eq; cases eq with | refl => rfl
  triangle _ _ := LambekD.triangle.{u, u, u, u}
  pentagon _ _ _ _ := LambekD.pentagon

end LambekD
