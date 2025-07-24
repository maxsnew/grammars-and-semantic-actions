import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.Data.List.Basic

import LambekD.Grammar
import LambekD.CategoryTheory.Biclosed.Monoidal

universe u
variable [AlphabetStr]
open AlphabetStr
open CategoryTheory
open MonoidalCategory

--------------------------------------------------------------------------------
-- Monoidal Structure
--------------------------------------------------------------------------------
structure Splitting (w : SemString) where
 left : SemString
 right : SemString
 concatEq : left ++ right = w

@[simp]
def eqSplit (w w' : SemString) : Splitting (w ++ w') :=
  Splitting.mk w w' (refl _)

@[ext]
def Splitting.ext {w : SemString} {s s' : Splitting w} :
  s.left = s'.left → s.right = s'.right → s = s' := by
 intro hl hr
 cases s with
 | mk left right concatEq =>
  cases s' with
  | mk left' right' concatEq' =>
    simp at hl hr
    subst hl hr
    rfl

structure TensorTy (A B : SemGrammar) (w : SemString) where
 split : Splitting w
 left : A (split.left)
 right : B (split.right)

@[simp]
def Tensor (A B : SemGrammar) : SemGrammar := λ (w : SemString) => TensorTy A B w

@[ext]
def Tensor.ext {w : SemString} {A B : SemGrammar} {ab ab' : Tensor A B w} :
  (sEql : ab.split.left = ab'.split.left) →
  (sEqr : ab.split.right = ab'.split.right) →
  ab.left ≍ ab'.left → ab.right ≍ ab'.right → ab = ab' := by
   intro sEql sEqr abl abr
   have sEq : ab.split = ab'.split := by
    apply Splitting.ext
    · exact sEql
    · exact sEqr
   cases ab with
   | mk s l r =>
    cases ab' with
    | mk s' l' r' =>
     simp at sEq abl abr
     subst sEq abl abr
     rfl

@[simp]
def SemLiteral (c : Alphabet) : SemGrammar := λ w => ULift (PLift (w = [ c ]))

@[simp]
def LiteralIntro : {w : SemString} → {c : Alphabet} → (w = [ c ]) → SemLiteral c w :=
 fun p => ULift.up (PLift.up p)

@[simp]
def Epsilon : SemGrammar := λ (w : SemString) => ULift (PLift (w = List.nil))

@[simp]
def EpsilonIntro : {w : SemString } → (w = List.nil) → Epsilon w :=
 fun p => ULift.up (PLift.up p)

@[simp]
def EpsilonUnitR : {A : SemGrammar} → Tensor A Epsilon ⟶ A :=
 fun w ⟨⟨l, r, ce⟩ , a , ⟨⟨nil⟩⟩⟩ =>
  let lw : l = w := by
   simp at nil
   rw [nil] at ce
   simp at ce
   exact ce
  Eq.rec a lw

@[simp]
def EpsilonUnitRInv : {A : SemGrammar} → A ⟶ Tensor A Epsilon :=
 fun w a =>
   let split := {left := w, right := [], concatEq := by simp}
   let eps := EpsilonIntro (Eq.refl [])
   ⟨split, a, eps⟩

@[simp]
def EpsilonUnitL : {A : SemGrammar} → Tensor Epsilon A ⟶ A :=
 fun w ⟨s , ⟨⟨nil⟩⟩ , a⟩ =>
 have p : s.right = w := by
  let x := s.concatEq
  rw [nil] at x
  simp at x
  exact x
 p ▸ a

@[simp]
def EpsilonUnitLInv : {A : SemGrammar} → A ⟶ Tensor Epsilon A :=
 fun w a =>
   let split := {left := [], right := w, concatEq := by simp}
   let eps := EpsilonIntro (Eq.refl [])
   ⟨split, eps, a⟩

@[simp]
def TensorIn {A B C D : SemGrammar} : (A ⟶ B) → (C ⟶ D) → (Tensor A C ⟶ Tensor B D) :=
 fun f g _ ⟨s , a , c⟩ => ⟨s, f s.left a, g s.right c⟩

@[simp]
def TensorAssoc {A B C : SemGrammar } : Tensor (Tensor A B) C ⟶ Tensor A (Tensor B C) :=
 fun _ ⟨s, ⟨s' , a , b⟩ , c⟩ =>
 let split := {left := s'.left, right := s'.right ++ s.right, concatEq := by rw [← List.append_assoc]; rw [s'.concatEq]; rw [s.concatEq]}
 let split' := {left := s'.right, right := s.right, concatEq := by tauto}
 ⟨split, a, ⟨split', b , c⟩⟩

@[simp]
def TensorAssocInv {A B C : SemGrammar } : Tensor A (Tensor B C) ⟶ Tensor (Tensor A B) C :=
 fun _ ⟨s, a , ⟨s' , b , c⟩⟩ =>
 let split := {left := s.left ++ s'.left, right := s'.right, concatEq := by simp; rw [s'.concatEq]; rw [s.concatEq]}
 let split' := {left := s.left, right := s'.left, concatEq := by tauto}
 ⟨split, ⟨split', a, b⟩, c⟩

set_option pp.proofs true
instance : MonoidalCategory SemGrammar where
 tensorObj := Tensor
 whiskerLeft A B C f _ := fun ⟨s , a , b⟩ => ⟨s , a, f _ b⟩
 whiskerRight {A} {B} f C _ := fun ⟨s , a , c⟩ => ⟨s , f _ a , c⟩
 tensorUnit := Epsilon
 associator A B C := {
  hom := TensorAssoc ,
  inv := TensorAssocInv ,
  hom_inv_id := by
   funext w ⟨⟨l, r, ce⟩, ⟨⟨l', r', ce'⟩ , a , b⟩, c⟩
   cases ce with | refl => cases ce' with | refl => tauto
  inv_hom_id := by
   funext w ⟨⟨l, r, ce⟩, a , ⟨l', r', ce'⟩ , b , c⟩
   cases ce with | refl => cases ce' with | refl => tauto
 }
 associator_naturality f g h := by
   funext w ⟨⟨l, r, ce⟩, ⟨⟨l', r', ce'⟩ , a , b⟩, c⟩
   cases ce with | refl => cases ce' with | refl => tauto
 leftUnitor A := {
  hom := EpsilonUnitL
  inv := EpsilonUnitLInv
  hom_inv_id := by
   funext w ⟨⟨l, r, ce⟩, ⟨⟨nil⟩⟩ , a⟩
   cases ce with | refl => cases nil with | refl => tauto
 }
 leftUnitor_naturality f := by
   funext w ⟨⟨l, r, ce⟩, ⟨⟨nil⟩⟩ , a⟩
   cases ce with | refl => cases nil with | refl => tauto
 rightUnitor A := {
  hom := EpsilonUnitR
  inv := EpsilonUnitRInv
  hom_inv_id := by
   funext w ⟨⟨l, r, ce⟩, a, ⟨⟨nil⟩⟩⟩
   cases ce with | refl => cases nil with | refl =>
    simp
 }
 rightUnitor_naturality f := by
   funext w ⟨⟨l, r, ce⟩, a, ⟨⟨nil⟩⟩⟩
   simp [EpsilonUnitR, CategoryStruct.comp, CategoryStruct.id, pi]
   simp at a nil
   let x := EpsilonUnitR._proof_1 w l r ce nil
   have h : l = w := x
   rw [← h] at x
   cases x with | refl =>
    subst h
    rfl
 triangle A B := by
  funext w ⟨⟨l, r, ce⟩, ⟨⟨l', r', ce'⟩, a, ⟨⟨nil⟩⟩⟩, b⟩
  cases nil with | refl => cases ce with | refl => cases ce' with | refl =>
   simp
 pentagon A B C D := by
  funext w ⟨⟨l, r, ce⟩, ⟨⟨l', r', ce'⟩, ⟨⟨l'', r'', ce''⟩, a, b⟩, c⟩, d⟩
  simp
  cases ce with | refl => cases ce' with | refl => cases ce'' with | refl =>
    simp at a b c d
    grind
    -- TODO : ask on zulip

--------------------------------------------------------------------------------
-- Linear Functions
--------------------------------------------------------------------------------

@[simp]
def rightClosure (A : SemGrammar) : SemGrammar ⥤ SemGrammar where
  obj B w := ∀ (w' : SemString), A w' → B (w' ++ w)
  map f w g w' a := f _ (g _ a)

@[simp]
def rightClosureAdj (A : SemGrammar) : tensorLeft A ⊣ rightClosure A where
  unit := {
    app B w b w' a := TensorTy.mk (eqSplit w' w) a b
    naturality B C f := by
      funext w b w' a
      simp[MonoidalCategoryStruct.whiskerLeft]
  }
  counit := {
    app B w x := match x with
                 | TensorTy.mk ⟨l, r, ce⟩ a b => by
                   exact Eq.rec (b l a) ce
    naturality B C f := by
      funext w ⟨⟨l, r, ce⟩, a, b⟩
      simp[MonoidalCategoryStruct.whiskerLeft]
      cases ce with | refl => simp
  }
  left_triangle_components B := by
    simp[MonoidalCategoryStruct.whiskerLeft]
    funext w ⟨⟨l, r, ce⟩, a, b⟩
    cases ce with | refl => simp
  right_triangle_components B := by
    simp[MonoidalCategoryStruct.whiskerLeft]
    funext w f
    simp

instance : MonoidalRightClosed SemGrammar where
  right_closed A := {
    rightAdj := rightClosure A
    adj := rightClosureAdj A
  }

@[simp]
def leftClosure (A : SemGrammar) : SemGrammar ⥤ SemGrammar where
  obj B w := ∀ (w' : SemString), A w' → B (w ++ w')
  map f w g w' a := f _ (g _ a)

@[simp]
def leftClosureAdj (A : SemGrammar) : tensorRight A ⊣ leftClosure A where
  unit := {
    app B w b w' a := TensorTy.mk (eqSplit w w') b a
    naturality B C f := by
      funext w b w' a
      simp[MonoidalCategoryStruct.whiskerRight]
  }
  counit := {
    app B w x := match x with
                 | TensorTy.mk ⟨l, r, ce⟩ b a => by
                   exact Eq.rec (b r a) ce
    naturality B C f := by
      funext w ⟨⟨l, r, ce⟩, a, b⟩
      simp[MonoidalCategoryStruct.whiskerLeft]
      cases ce with | refl => simp
  }
  left_triangle_components B := by
    simp[MonoidalCategoryStruct.whiskerLeft]
    funext w ⟨⟨l, r, ce⟩, a, b⟩
    cases ce with | refl => simp
  right_triangle_components B := by
    simp[MonoidalCategoryStruct.whiskerLeft]
    funext w f
    simp

instance : MonoidalLeftClosed SemGrammar where
  left_closed A := {
    rightAdj := leftClosure A
    adj := leftClosureAdj A
  }

instance : MonoidalBiclosed SemGrammar where
  biclosed _ := {left_closed := inferInstance, right_closed := inferInstance}

-- -- ⊸
-- @[simp]
-- def LinearFunctionL (A B : SemGrammar.{u}) : SemGrammar.{u} :=
--   λ (w : SemString.{u}) => ∀ (w' : SemString), A w' → B (w ++ w')

-- @[simp]
-- def LinearFunctionLIn {A B C : SemGrammar.{u}} : (Tensor A B ⟶ C) → (A ⟶ LinearFunctionL B C) :=
--   fun f w a w' b => f (w ++ w') (TensorTy.mk (Splitting.mk w w' (refl _)) a b)

-- @[simp]
-- def LinearFunctionLApp {A B : SemGrammar.{u}} : (Tensor (LinearFunctionL A B) A ⟶ B) :=
--   fun _ ⟨⟨_, _, ce⟩, f, a⟩ => Eq.rec (f _ a) ce

-- -- ⟜
-- @[simp]
-- def LinearFunctionR (A B : SemGrammar.{u}) : SemGrammar.{u} :=
--   λ (w : SemString.{u}) => ∀ (w' : SemString), B w' → A (w' ++ w)

-- @[simp]
-- def LinearFunctionRIn {A B C : SemGrammar.{u}} : (Tensor A B ⟶ C) → (B ⟶ LinearFunctionR C A) :=
--   fun f w b w' a => f (w' ++ w) (TensorTy.mk (Splitting.mk w' w (refl _)) a b)

-- @[simp]
-- def LinearFunctionRApp {A B : SemGrammar.{u}} : Tensor A (LinearFunctionR B A) ⟶ B :=
--   fun _ ⟨⟨_, _, ce⟩, a, f⟩ => Eq.rec (f _ a) ce

-- -- TODO use CategoryTheory.Closed.Monoidal to show that these form a closed structure
-- -- for the above monoidal structure

-- --------------------------------------------------------------------------------
-- -- Elements of a grammar
-- -- ↑ : LinearTypes → NonLinearTypes
-- -- ↑ A := A []
-- --------------------------------------------------------------------------------

-- -- ↑
-- @[simp]
-- def Element (A : SemGrammar.{u}) : Type _ := A []
