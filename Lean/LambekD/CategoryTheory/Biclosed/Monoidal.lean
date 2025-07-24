-- TODO : merge this properly into mathlib
-- Refactor of Mathlib.CategoryTheory.Closed.Monoidal
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Daniel Carranza, Joël Riou
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Closed monoidal categories

Define left/right closed objects and left/right closed monoidal categories.
A biclosed monoidal category is one that is both left and right closed.

## TODO
- Some of the theorems proved about cartesian closed categories
  should be generalised and moved to this file.

- Build the left closed structures in terms of the right ones by composing
  with flip of a Bifunctor
-/


universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

-- Note that this class carries a particular choice of right adjoint,
-- (which is only unique up to isomorphism),
-- not merely the existence of such, and
-- so definitional properties of instances may be important.
/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class RightClosed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

class LeftClosed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorRight X ⊣ rightAdj

class Biclosed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  right_closed : RightClosed X
  left_closed : LeftClosed X

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class MonoidalRightClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  right_closed (X : C) : RightClosed X := by infer_instance

class MonoidalLeftClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  left_closed (X : C) : LeftClosed X := by infer_instance

class MonoidalBiclosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  biclosed (X : C) : Biclosed X := by infer_instance

attribute [instance 100] MonoidalRightClosed.right_closed
attribute [instance 100] MonoidalLeftClosed.left_closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
def tensorRightClosed {X Y : C} (hX : RightClosed X) (hY : RightClosed Y) : RightClosed (X ⊗ Y) where
  rightAdj := RightClosed.rightAdj X ⋙ RightClosed.rightAdj Y
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

def tensorLeftClosed {X Y : C} (hX : LeftClosed X) (hY : LeftClosed Y) : LeftClosed (X ⊗ Y) where
  rightAdj := LeftClosed.rightAdj Y ⋙ LeftClosed.rightAdj X
  adj := (hX.adj.comp hY.adj).ofNatIsoLeft (MonoidalCategory.tensorRightTensor X Y).symm

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unitRightClosed : RightClosed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

def unitLeftClosed : LeftClosed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.rightUnitorNatIso C).symm


variable (A B : C) {X X' Y Y' Z : C}


open CategoryTheory.Limits

section
variable [RightClosed A]

/-- This is the right internal hom `- [C]← A`.
-/
def ihomR : C ⥤ C :=
  RightClosed.rightAdj (X := A)

namespace ihomR

/-- The adjunction between `A ⊗ -` and `- [C]← A`. -/
def adjunction : tensorLeft A ⊣ ihomR A :=
  RightClosed.adj

instance : (tensorLeft A).IsLeftAdjoint  :=
  (ihomR.adjunction A).isLeftAdjoint

/-- The evaluation natural transformation. -/
def ev : ihomR A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihomR.adjunction A).counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihomR A :=
  (ihomR.adjunction A).unit

@[simp]
theorem ihom_adjunction_counit : (ihomR.adjunction A).counit = ev A :=
  rfl

@[simp]
theorem ihom_adjunction_unit : (ihomR.adjunction A).unit = coev A :=
  rfl

@[reassoc (attr := simp)]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    A ◁ (ihomR A).map f ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[reassoc (attr := simp)]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihomR A).map (A ◁ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the right internal hom from `A` to `B` -/
notation B " [" C "]← " A:10 => (@ihomR C _ _ A _).obj B

@[reassoc (attr := simp)]
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  (ihomR.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
theorem coev_ev : (coev A).app (B [C]← A) ≫ (ihomR A).map ((ev A).app B) = 𝟙 (B [C]← A) :=
  Adjunction.right_triangle_components (ihomR.adjunction A) _

end ihomR

instance : PreservesColimits (tensorLeft A) :=
  (ihomR.adjunction A).leftAdjoint_preservesColimits

end

section
variable [LeftClosed A]

/-- This is the left internal hom `A ⟶[C] -`.
-/
def ihomL : C ⥤ C :=
  LeftClosed.rightAdj (X := A)

namespace ihomL

/-- The adjunction between `- ⊗ A` and `A →[C] -`. -/
def adjunction : tensorRight A ⊣ ihomL A :=
  LeftClosed.adj

instance : (tensorRight A).IsLeftAdjoint  :=
  (ihomL.adjunction A).isLeftAdjoint

/-- The evaluation natural transformation. -/
def ev : ihomL A ⋙ tensorRight A ⟶ 𝟭 C :=
  (ihomL.adjunction A).counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensorRight A ⋙ ihomL A :=
  (ihomL.adjunction A).unit

@[simp]
theorem ihom_adjunction_counit : (ihomL.adjunction A).counit = ev A :=
  rfl

@[simp]
theorem ihom_adjunction_unit : (ihomL.adjunction A).unit = coev A :=
  rfl

@[reassoc (attr := simp)]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    (ihomL A).map f ▷ A ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[reassoc (attr := simp)]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihomL A).map (f ▷ A) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the left internal hom from `A` to `B` -/
notation A " →[" C "] " B:10 => (@ihomL C _ _ A _).obj B

@[reassoc (attr := simp)]
theorem ev_coev : ((coev A).app B ▷ A) ≫ (ev A).app (B ⊗ A) = 𝟙 (B ⊗ A) :=
  (ihomL.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
theorem coev_ev : (coev A).app (A →[C] B) ≫ (ihomL A).map ((ev A).app B) = 𝟙 (A →[C] B) :=
  Adjunction.right_triangle_components (ihomL.adjunction A) _

end ihomL


instance : PreservesColimits (tensorRight A) :=
  (ihomL.adjunction A).leftAdjoint_preservesColimits

end

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace MonoidalRightClosed
variable [RightClosed A]

/-- Currying in a monoidal closed category. -/
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ X [C]← A) :=
  (ihomR.adjunction A).homEquiv _ _

/-- Uncurrying in a monoidal closed category. -/
def uncurry : (Y ⟶ X [C]← A) → (A ⊗ Y ⟶ X) :=
  ((ihomR.adjunction A).homEquiv _ _).symm

theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (ihomR.adjunction A).homEquiv _ _ f = curry f :=
  rfl

theorem homEquiv_symm_apply_eq (f : Y ⟶ X [C]← A) :
    ((ihomR.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihomR _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ Y [C]← A) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihomR _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ Y [C]← A) :
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (RightClosed.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ Y [C]← A) : curry (uncurry f) = f :=
  (RightClosed.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ X [C]← A) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihomR.adjunction A) f g

theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ X [C]← A) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihomR.adjunction A) f g

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ X [C]← A) : uncurry g = (A ◁ g) ≫ (ihomR.ev A).app X := by
  rfl

theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihomR.coev A).app Y ≫ (ihomR A).map g :=
  rfl

theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ X [C]← A)) :=
  (RightClosed.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ X [C]← A) → (A ⊗ Y ⟶ X)) :=
  (RightClosed.adj.homEquiv _ _).symm.injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (X [C]← A)) = (ihomR.ev A).app X := by
  simp [uncurry_eq]

theorem curry_id_eq_coev : curry (𝟙 _) = (ihomR.coev A).app X := by
  rw [curry_eq, (ihomR A).map_id (A ⊗ _)]
  apply comp_id

@[reassoc (attr := simp)]
lemma whiskerLeft_curry_ihomR_ev_app (g : A ⊗ Y ⟶ X) :
    A ◁ curry g ≫ (ihomR.ev A).app X = g := by
  simp [curry_eq]

theorem uncurry_ihomR_map (g : Y ⟶ Y') :
    uncurry ((ihomR A).map g) = (ihomR.ev A).app Y ≫ g := by
  apply curry_injective
  rw [curry_uncurry, curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, id_comp]

/-- The internal hom out of the unit is naturally isomorphic to the identity functor. -/
def unitNatIso [RightClosed (𝟙_ C)] : 𝟭 C ≅ ihomR (𝟙_ C) :=
  conjugateIsoEquiv (Adjunction.id (C := C)) (ihomR.adjunction (𝟙_ C))
    (leftUnitorNatIso C)
section Pre

variable {A B}
variable [RightClosed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihomR A ⟶ ihomR B :=
  conjugateEquiv (ihomR.adjunction _) (ihomR.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    B ◁ (pre f).app X ≫ (ihomR.ev B).app X = f ▷ (X [C]← A) ≫ (ihomR.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalRightClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihomR.ev A).app X := by
  simp [uncurry_eq]

@[reassoc]
lemma curry_pre_app (f : B ⟶ A) {X Y : C} (g : A ⊗ Y ⟶ X) :
    curry g ≫ (pre f).app X = curry (f ▷ _ ≫ g) := uncurry_injective (by
  rw [uncurry_curry, uncurry_eq, MonoidalCategory.whiskerLeft_comp, assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whiskerLeft_curry_ihomR_ev_app])

@[reassoc (attr := simp)]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihomR.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihomR.coev B).app X ≫ (ihomR B).map (f ▷ _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[reassoc]
lemma uncurry_pre_app (f : Y ⟶ X [C]← A) (g : B ⟶ A) :
    uncurry (f ≫ (pre g).app X) = g ▷ _ ≫ uncurry f :=
  curry_injective (by
    rw [curry_uncurry, ← curry_pre_app, curry_uncurry])

@[simp]
theorem pre_id (A : C) [RightClosed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre, Functor.map_id]
  apply conjugateEquiv_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [RightClosed A₁] [RightClosed A₂] [RightClosed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, (tensoringLeft C).map_comp]

theorem pre_comm_ihomR_map {W X Y Z : C} [RightClosed W] [RightClosed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihomR W).map g = (ihomR X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
def internalHomR [MonoidalRightClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihomR X.unop
  map f := pre f.unop

/-- The parametrized adjunction between `curriedTensor C : C ⥤ C ⥤ C`
and `internalHomR : Cᵒᵖ ⥤ C ⥤ C` -/
@[simps!]
def internalHomRAdjunction₂ [MonoidalRightClosed C] :
    curriedTensor C ⊣₂ internalHomR where
  adj _ := ihomR.adjunction _

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable (F : C ⥤ D) {G : D ⥤ C} (adj : F ⊣ G)
  [F.Monoidal] [F.IsEquivalence] [MonoidalRightClosed D]

/-- Transport the property of being monoidal closed across a monoidal equivalence of categories -/
noncomputable def ofEquiv : MonoidalRightClosed C where
  right_closed X :=
    { rightAdj := F ⋙ ihomR (F.obj X) ⋙ G
      adj := (adj.comp ((ihomR.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting currying map `Hom(X ⊗ Y, Z) → Hom(Y, (X ⟶[C] Z))`. (`X ⟶[C] Z` is defined to be
`F⁻¹(F(X) ⟶[D] F(Z))`, so currying in `C` is given by essentially conjugating currying in
`D` by `F.`) -/
theorem ofEquiv_curry_def {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    letI := ofEquiv F adj
    MonoidalRightClosed.curry f =
      adj.homEquiv Y ((ihomR (F.obj X)).obj (F.obj Z))
        (MonoidalRightClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X ⊗ F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).hom.app Y ≫ f))) := by
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change ((adj.comp ((ihomR.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _ _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting uncurrying map `Hom(Y, (X ⟶[C] Z)) → Hom(X ⊗ Y ⟶ Z)`. (`X ⟶[C] Z` is
defined to be `F⁻¹(F(X) ⟶[D] F(Z))`, so uncurrying in `C` is given by essentially conjugating
uncurrying in `D` by `F.`) -/
theorem ofEquiv_uncurry_def {X Y Z : C} :
    letI := ofEquiv F adj
    ∀ (f : Y ⟶ (ihomR X).obj Z), MonoidalRightClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalRightClosed.uncurry ((adj.homEquiv _ _).symm f)) := by
  intro f
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change (((adj.comp ((ihomR.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _).symm _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

end OfEquiv

end MonoidalRightClosed

namespace MonoidalLeftClosed
variable [LeftClosed A]

/-- Currying in a monoidal closed category. -/
def curry : (Y ⊗ A ⟶ X) → (Y ⟶ A →[C] X) :=
  (ihomL.adjunction A).homEquiv _ _

/-- Uncurrying in a monoidal closed category. -/
def uncurry : (Y ⟶ A →[C] X) → (Y ⊗ A ⟶ X) :=
  ((ihomL.adjunction A).homEquiv _ _).symm

theorem homEquiv_apply_eq (f : Y ⊗ A ⟶ X) : (ihomL.adjunction A).homEquiv _ _ f = curry f :=
  rfl

theorem homEquiv_symm_apply_eq (f : Y ⟶ A →[C] X) :
    ((ihomL.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : X' ⊗ A ⟶ Y) : curry (f ▷ _ ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : X ⊗ A ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihomL _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A →[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihomL _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A →[C] Y) :
    uncurry (f ≫ g) = f ▷ _ ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : X ⊗ A ⟶ Y) : uncurry (curry f) = f :=
  (LeftClosed.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A →[C] Y) : curry (uncurry f) = f :=
  (LeftClosed.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : Y ⊗ A ⟶ X) (g : Y ⟶ A →[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihomL.adjunction A) f g

theorem eq_curry_iff (f : Y ⊗ A ⟶ X) (g : Y ⟶ A →[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihomL.adjunction A) f g

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A →[C] X) : uncurry g = (g ▷ A) ≫ (ihomL.ev A).app X := by
  rfl

theorem curry_eq (g : Y ⊗ A ⟶ X) : curry g = (ihomL.coev A).app Y ≫ (ihomL A).map g :=
  rfl

theorem curry_injective : Function.Injective (curry : (Y ⊗ A ⟶ X) → (Y ⟶ A →[C] X)) :=
  (LeftClosed.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A →[C] X) → (Y ⊗ A ⟶ X)) :=
  (LeftClosed.adj.homEquiv _ _).symm.injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (A →[C] X)) = (ihomL.ev A).app X := by
  simp [uncurry_eq]

theorem curry_id_eq_coev : curry (𝟙 _) = (ihomL.coev A).app X := by
  rw [curry_eq, (ihomL A).map_id (_ ⊗ A)]
  apply comp_id

@[reassoc (attr := simp)]
lemma whiskerRight_curry_ihomL_ev_app (g : Y ⊗ A ⟶ X) :
    curry g ▷ A ≫ (ihomL.ev A).app X = g := by
  simp [curry_eq]

theorem uncurry_ihomL_map (g : Y ⟶ Y') :
    uncurry ((ihomL A).map g) = (ihomL.ev A).app Y ≫ g := by
  apply curry_injective
  rw [curry_uncurry, curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, id_comp]

/-- The internal hom out of the unit is naturally isomorphic to the identity functor. -/
def unitNatIso [LeftClosed (𝟙_ C)] : 𝟭 C ≅ ihomL (𝟙_ C) :=
  conjugateIsoEquiv (Adjunction.id (C := C)) (ihomL.adjunction (𝟙_ C))
    (rightUnitorNatIso C)
section Pre

variable {A B}
variable [LeftClosed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihomL A ⟶ ihomL B :=
  conjugateEquiv (ihomL.adjunction _) (ihomL.adjunction _) ((tensoringRight C).map f)

@[reassoc (attr := simp)]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    (pre f).app X ▷ B ≫ (ihomL.ev B).app X = ((A →[C] X) ◁ f) ≫ (ihomL.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringRight C).map f) X

@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalLeftClosed.uncurry ((pre f).app X) = _ ◁ f ≫ (ihomL.ev A).app X := by
  simp [uncurry_eq]

@[reassoc]
lemma curry_pre_app (f : B ⟶ A) {X Y : C} (g : Y ⊗ A ⟶ X) :
    curry g ≫ (pre f).app X = curry (_ ◁ f ≫ g) := uncurry_injective (by
  rw [uncurry_curry, uncurry_eq, MonoidalCategory.comp_whiskerRight, assoc,
    id_tensor_pre_app_comp_ev, ← whisker_exchange_assoc, whiskerRight_curry_ihomL_ev_app])

@[reassoc (attr := simp)]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihomL.coev A).app X ≫ (pre f).app (X ⊗ A) = (ihomL.coev B).app X ≫ (ihomL B).map (_ ◁ f) :=
  unit_conjugateEquiv _ _ ((tensoringRight C).map f) X

@[reassoc]
lemma uncurry_pre_app (f : Y ⟶ A →[C] X) (g : B ⟶ A) :
    uncurry (f ≫ (pre g).app X) = _ ◁ g ≫ uncurry f :=
  curry_injective (by
    rw [curry_uncurry, ← curry_pre_app, curry_uncurry])

@[simp]
theorem pre_id (A : C) [LeftClosed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre, Functor.map_id]
  apply conjugateEquiv_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [LeftClosed A₁] [LeftClosed A₂] [LeftClosed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, (tensoringRight C).map_comp]

theorem pre_comm_ihomL_map {W X Y Z : C} [LeftClosed W] [LeftClosed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihomL W).map g = (ihomL X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
def internalHomL [MonoidalLeftClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihomL X.unop
  map f := pre f.unop

/-- The parametrized adjunction between `curriedTensor C : C ⥤ C ⥤ C`
and `internalHomL : Cᵒᵖ ⥤ C ⥤ C` -/
@[simps!]
def internalHomLAdjunction₂ [MonoidalLeftClosed C] :
    (curriedTensor C).flip ⊣₂ internalHomL where
  adj _ := ihomL.adjunction _

-- TODO ofEquiv for ihomL

end MonoidalLeftClosed
