import LambekD.Grammar.Cat
import LambekD.Grammar.Tensor
import LambekD.Tactic

import Mathlib.CategoryTheory.Monoidal.Category

/-! # Monoidal category instance for Grammar

The tensor product `⊗` and unit `ε` equip `Grammar` with a monoidal
category structure. Coherence (pentagon, triangle, naturality) reuses the
algebraic laws proved in `Grammar.Tensor`.

Note: `uAlph = uGram` is required so that `GTensor A B` (which includes a `Splitting`
containing strings in `Type uAlph`) lands in `Grammar`. Both are parameterized
by a single universe `u`.
-/

namespace LambekD

universe u

open CategoryTheory MonoidalCategory
variable {Alphabet : Type u}

instance : MonoidalCategory (Grammar.{u, u} Alphabet) where
  tensorObj := GTensor
  whiskerLeft X _ _ f := gtensorIntro (gId X) f
  whiskerRight f Z := gtensorIntro f (gId Z)
  tensorUnit := ε
  associator A B C := {
    hom := gtensorAssoc
    inv := gtensorAssocInv
    hom_inv_id := gtensorAssocInv_inv
    inv_hom_id := gtensorAssoc_inv
  }
  associator_naturality {_ _ _ _ _ _} _ _ _ := by grammar_ext
  leftUnitor A := {
    hom := gεUnitL.{u, u, u}
    inv := gεUnitLInv.{u, u, u}
    hom_inv_id := gεUnitLInv_comp.{u, u, u}
    inv_hom_id := gεUnitL_inv_comp.{u, u, u}
  }
  leftUnitor_naturality _ := by
    funext w ⟨⟨l, r, eq⟩, ⟨⟨nil⟩⟩, a⟩
    cases nil with | refl => cases eq with | refl => rfl
  rightUnitor A := {
    hom := gεUnitR.{u, u, u}
    inv := gεUnitRInv.{u, u, u}
    hom_inv_id := gεUnitRInv_comp.{u, u, u}
    inv_hom_id := gεUnitR_inv_comp.{u, u, u}
  }
  rightUnitor_naturality _ := by
    funext w ⟨⟨l, r, eq⟩, a, ⟨⟨nil⟩⟩⟩
    cases nil with | refl => simp at eq; cases eq with | refl => rfl
  triangle _ _ := LambekD.triangle.{u, u, u, u}
  pentagon _ _ _ _ := LambekD.pentagon

end LambekD
