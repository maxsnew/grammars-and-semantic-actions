import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.List.Basic
import LambekD.Grammar

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

--------------------------------------------------------------------------------
-- Monoidal Structure
--------------------------------------------------------------------------------
structure Splitting (w : SemString.{u}) : Type u where
 left : SemString
 right : SemString
 concatEq : left ++ right = w

@[ext]
def Splitting.ext {w : SemString.{u}} {s s' : Splitting w} :
  s.left = s'.left → s.right = s'.right → s = s' := by
 intro hl hr
 cases s with
 | mk left right concatEq =>
  cases s' with
  | mk left' right' concatEq' =>
    simp at hl hr
    subst hl hr
    rfl

structure TensorTy (A B : SemGrammar.{u}) (w : SemString) : Type (u + 1) where
 split : Splitting w
 left : A (split.left)
 right : B (split.right)

def Tensor (A B : SemGrammar.{u}) : SemGrammar.{u} := λ (w : SemString.{u}) => TensorTy.{u} A B w

@[ext]
def Tensor.ext {w : SemString } {A B : SemGrammar } {ab ab' : Tensor A B w} :
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

def SemLiteral (c : Alphabet) : SemGrammar := λ w => ULift (PLift (w = [ c ]))

def LiteralIntro : {w : SemString} → {c : Alphabet} → (w = [ c ]) → SemLiteral c w :=
 fun p => ULift.up (PLift.up p)

def Epsilon : SemGrammar := λ (w : SemString) => ULift (PLift (w = List.nil))

def EpsilonIntro : {w : SemString } → (w = List.nil) → Epsilon w :=
 fun p => ULift.up (PLift.up p)

def EpsilonUnitR : {A : SemGrammar} →
 Reduction (Tensor A (Epsilon )) A :=
 fun w ⟨⟨l, r, ce⟩ , a , ⟨⟨nil⟩⟩⟩ =>
  let lw : l = w := by
   simp at nil
   rw [nil] at ce
   simp at ce
   exact ce
  Eq.rec a lw

def EpsilonUnitRInv : {A : SemGrammar} →
 Reduction A (Tensor A (Epsilon )) :=
 fun w a =>
   let split := {left := w, right := [], concatEq := by simp}
   let eps := EpsilonIntro (Eq.refl [])
   ⟨split, a, eps⟩

def EpsilonUnitL : {A : SemGrammar} →
 Reduction (Tensor (Epsilon ) A) A :=
 fun w ⟨s , ⟨⟨nil⟩⟩ , a⟩ =>
 have p : s.right = w := by
  let x := s.concatEq
  rw [nil] at x
  simp at x
  exact x
 p ▸ a

def EpsilonUnitLInv : {A : SemGrammar} →
 Reduction A (Tensor (Epsilon ) A) :=
 fun w a =>
   let split := {left := [], right := w, concatEq := by simp}
   let eps := EpsilonIntro (Eq.refl [])
   ⟨split, eps, a⟩

def TensorIn {A B C D : SemGrammar} :
Reduction A B → Reduction C D →
 Reduction (Tensor A C) (Tensor B D) :=
 fun f g _ ⟨s , a , c⟩ => ⟨s, f s.left a, g s.right c⟩

def TensorAssoc {A B C : SemGrammar } :
 Reduction (Tensor (Tensor A B) C) (Tensor A (Tensor B C)) :=
 fun _ ⟨s, ⟨s' , a , b⟩ , c⟩ =>
 let split := {left := s'.left, right := s'.right ++ s.right, concatEq := by rw [← List.append_assoc]; rw [s'.concatEq]; rw [s.concatEq]}
 let split' := {left := s'.right, right := s.right, concatEq := by tauto}
 ⟨split, a, ⟨split', b , c⟩⟩

def TensorAssocInv {A B C : SemGrammar } :
 Reduction (Tensor A (Tensor B C)) (Tensor (Tensor A B) C) :=
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
    simp [EpsilonUnitR, EpsilonUnitRInv, CategoryStruct.comp, CategoryStruct.id, instCategorySemGrammar, pi]
    ext
    · simp
    · simp
    · simp
    · tauto
 }
 rightUnitor_naturality f := by
   funext w ⟨⟨l, r, ce⟩, a, ⟨⟨nil⟩⟩⟩
   simp [EpsilonUnitR, CategoryStruct.comp, CategoryStruct.id, instCategorySemGrammar, pi]
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
   simp [EpsilonUnitR, EpsilonUnitRInv, TensorAssoc, CategoryStruct.comp, CategoryStruct.id, instCategorySemGrammar, pi]
   ext
   · simp
   · simp
   · simp
   · simp [EpsilonUnitL]
 pentagon A B C D := by
  funext w ⟨⟨l, r, ce⟩, ⟨⟨l', r', ce'⟩, ⟨⟨l'', r'', ce''⟩, a, b⟩, c⟩, d⟩
  simp
  cases ce with | refl => cases ce' with | refl => cases ce'' with | refl =>
   simp
   simp [EpsilonUnitR, EpsilonUnitRInv, TensorAssoc, CategoryStruct.comp, CategoryStruct.id, instCategorySemGrammar, pi]
   simp at a b c d
   ext
   · simp
   · simp
   · simp
   · simp
     -- TODO: Stuck on this because I don't know how to match on intermediate concatEq proofs
     sorry

--------------------------------------------------------------------------------
-- Linear Functions
--------------------------------------------------------------------------------

-- ⊸
def LinearFunctionL (A B : SemGrammar.{u}) : SemGrammar.{u} :=
  λ (w : SemString.{u}) => ∀ (w' : SemString), A w' → B (w ++ w')

def LinearFunctionLIn {A B C : SemGrammar.{u}} :
  Reduction (Tensor A B) C → Reduction A (LinearFunctionL B C) :=
  fun f w a w' b => f (w ++ w') (TensorTy.mk (Splitting.mk w w' (refl _)) a b)

def LinearFunctionLApp {A B : SemGrammar.{u}} :
  Reduction (Tensor (LinearFunctionL A B) A) B :=
  fun _ ⟨⟨_, _, ce⟩, f, a⟩ => Eq.rec (f _ a) ce

-- ⟜
def LinearFunctionR (A B : SemGrammar.{u}) : SemGrammar.{u} :=
  λ (w : SemString.{u}) => ∀ (w' : SemString), B w' → A (w' ++ w)

def LinearFunctionRIn {A B C : SemGrammar.{u}} :
  Reduction (Tensor A B) C → Reduction B (LinearFunctionR C A) :=
  fun f w b w' a => f (w' ++ w) (TensorTy.mk (Splitting.mk w' w (refl _)) a b)

def LinearFunctionRApp {A B : SemGrammar.{u}} :
  Reduction (Tensor A (LinearFunctionR B A)) B :=
  fun _ ⟨⟨_, _, ce⟩, a, f⟩ => Eq.rec (f _ a) ce

-- TODO use CategoryTheory.Closed.Monoidal to show that these form a closed structure
-- for the above monoidal structure

--------------------------------------------------------------------------------
-- Elements of a grammar
-- ↑ : LinearTypes → NonLinearTypes
-- ↑ A := A []
--------------------------------------------------------------------------------

-- ↑
def Element (A : SemGrammar.{u}) : Type _ := A []
