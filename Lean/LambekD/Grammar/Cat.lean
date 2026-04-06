import LambekD.Core.Defs
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types

/-! # Category instance for Grammar

`Grammar = String → Type` inherits a category structure from `CategoryTheory.Pi`
(the functor category) where:
- Objects: `Grammar` (functions `String → Type`)
- Morphisms: `A ⟶ B = ∀ w, A w → B w` (= `A ⊢ B`)
-/

namespace LambekD

open CategoryTheory

universe uAlph

variable {Alphabet : Type uAlph}

-- Grammar already has a Category instance via Pi + Types.
-- Verify the morphisms match our grammar terms.
theorem hom_eq_term (A B : Grammar Alphabet) : (A ⟶ B) = (A ⊢ B) := rfl

theorem comp_eq_gComp {A B C : Grammar Alphabet} (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ g = g ∘g f := rfl

theorem id_eq_gId (A : Grammar Alphabet) : 𝟙 A = gId A := rfl

end LambekD
