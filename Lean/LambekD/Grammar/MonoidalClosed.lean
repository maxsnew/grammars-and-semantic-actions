import LambekD.Grammar.Monoidal
import LambekD.Grammar.FunctionR
import LambekD.Grammar.FunctionL
import LambekD.CategoryTheory.Biclosed.Monoidal

/-! # Monoidal closed structure for Grammar

The right linear function `A ⊸ B` and left linear function `B ⟜ A` give
`Grammar` a biclosed monoidal category structure: `tensorRight A ⊣ rightClosure A`
and `tensorLeft A ⊣ leftClosure A`.
-/

namespace LambekD

universe u

open CategoryTheory MonoidalCategory
variable {Alphabet : Type u}

/-- The right internal hom functor: `B ↦ A ⊸ B` -/
def rightClosureFunctor (A : Grammar.{u, u} Alphabet) : Grammar.{u, u} Alphabet ⥤ Grammar.{u, u} Alphabet where
  obj B := FunctionR A B
  map f := limpRIntro (f ∘g limpRApp)

/-- The adjunction `tensorRight A ⊣ rightClosureFunctor A` witnessing
    that `A ⊸ -` is right adjoint to `- ⊗ A`. -/
def rightClosureAdj (A : Grammar.{u, u} Alphabet) : tensorRight A ⊣ rightClosureFunctor A where
  unit := {
    app B w b w' a := ⟨splitting w w', b, a⟩
    naturality _ _ _ := rfl
  }
  counit := {
    app B := limpRApp
    naturality _ _ f := by
      funext w ⟨⟨l, r, eq⟩, g, a⟩; cases eq with | refl => rfl
  }
  left_triangle_components B := by
    funext w ⟨⟨l, r, eq⟩, b, a⟩; cases eq with | refl => rfl
  right_triangle_components _ := rfl

instance : MonoidalLeftClosed (Grammar.{u, u} Alphabet) where
  left_closed A := {
    rightAdj := rightClosureFunctor A
    adj := rightClosureAdj A
  }

/-- The left internal hom functor: `B ↦ B ⟜ A` -/
def leftClosureFunctor (A : Grammar.{u, u} Alphabet) : Grammar.{u, u} Alphabet ⥤ Grammar.{u, u} Alphabet where
  obj B := FunctionL B A
  map f := limpLIntro (f ∘g limpLApp)

/-- The adjunction `tensorLeft A ⊣ leftClosureFunctor A` witnessing
    that `- ⟜ A` is right adjoint to `A ⊗ -`. -/
def leftClosureAdj (A : Grammar.{u, u} Alphabet) : tensorLeft A ⊣ leftClosureFunctor A where
  unit := {
    app B w b w' a := ⟨splitting w' w, a, b⟩
    naturality _ _ _ := rfl
  }
  counit := {
    app B := limpLApp
    naturality _ _ f := by
      funext w ⟨⟨l, r, eq⟩, a, g⟩; cases eq with | refl => rfl
  }
  left_triangle_components B := by
    funext w ⟨⟨l, r, eq⟩, a, b⟩; cases eq with | refl => rfl
  right_triangle_components _ := rfl

instance : MonoidalRightClosed (Grammar.{u, u} Alphabet) where
  right_closed A := {
    rightAdj := leftClosureFunctor A
    adj := leftClosureAdj A
  }

instance : MonoidalBiclosed (Grammar.{u, u} Alphabet) where
  biclosed _ := { left_closed := inferInstance, right_closed := inferInstance }

end LambekD
