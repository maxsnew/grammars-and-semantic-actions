import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.List.Basic

universe u

variable (Alphabet : Type u)
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]

open CategoryTheory

abbrev SemString := List Alphabet

-- TODO can use piEquivalencefunctordiscrete to show that SemGrammar is equivalent to (StringCat ⇒ Type)
def StringCat := CategoryTheory.Discrete (SemString Alphabet)

def SemGrammar := SemString Alphabet → Type (u + 1)

def Reduction (A B : SemGrammar Alphabet) := (w : SemString Alphabet) → A w → B w

def constFamily : SemString Alphabet → Type (u + 1) := fun _ => Type u

def FamilyOfTypes : (w : SemString Alphabet) → Category (constFamily Alphabet w) := fun _ => CategoryTheory.types

instance : Category (SemGrammar Alphabet) := pi (I := SemString Alphabet) _

open Limits

instance : HasColimits (SemGrammar Alphabet) := sorry

def IdReduction {A : SemGrammar Alphabet} : Reduction Alphabet A A := fun _ a => a

structure Splitting (w : SemString Alphabet) where
  left : SemString Alphabet
  right : SemString Alphabet
  concatEq : left ++ right = w

-- def Tensor (A B : SemGrammar Alphabet) : SemGrammar Alphabet :=
--   λ (w : SemString Alphabet) => (s : Splitting Alphabet w) × A (s.left) × B (s.right)

structure TensorTy (A B : SemGrammar Alphabet) (w : SemString Alphabet) where
  split : Splitting Alphabet w
  left : A (split.left)
  right : B (split.right)

def Tensor (A B : SemGrammar Alphabet) : SemGrammar Alphabet := λ (w : SemString Alphabet) => TensorTy Alphabet A B w

-- theorem Tensor.ext {A B : SemGrammar Alphabet} {w : SemString Alphabet}
--   (x y : Tensor Alphabet A B w) :
--   (hsplit : x.split = y.split) →
--   (hsplit ▸ x.left = y.left) →
--   (hsplit ▸ x.right = y.right) →
--   x = y := by
--   intro hsplit hleft hright
--   ext

def Epsilon : SemGrammar Alphabet := λ (w : SemString Alphabet) => ULift (PLift (w = List.nil))

def EpsilonIntro : {w : SemString Alphabet} → (w = List.nil) → Epsilon Alphabet w :=
  fun p => ULift.up (PLift.up p)

def EpsilonUnitR : {A : SemGrammar Alphabet} →
  Reduction Alphabet (Tensor Alphabet A (Epsilon Alphabet)) A :=
  fun w ⟨s , a , ⟨⟨nil⟩⟩⟩ =>
  have p : s.left = w := by
    let x := s.concatEq
    rw [nil] at x
    simp at x
    exact x
  p ▸ a

def EpsilonUnitRInv : {A : SemGrammar Alphabet} →
  Reduction Alphabet A (Tensor Alphabet A (Epsilon Alphabet)) :=
  fun w a =>
     let split := {left := w, right := [], concatEq := by simp}
     let eps := EpsilonIntro Alphabet (Eq.refl [])
     ⟨split, a, eps⟩

def EpsilonUnitL : {A : SemGrammar Alphabet} →
  Reduction Alphabet (Tensor Alphabet (Epsilon Alphabet) A) A :=
  fun w ⟨s , ⟨⟨nil⟩⟩ , a⟩ =>
  have p : s.right = w := by
    let x := s.concatEq
    rw [nil] at x
    simp at x
    exact x
  p ▸ a

def EpsilonUnitLInv : {A : SemGrammar Alphabet} →
  Reduction Alphabet A (Tensor Alphabet (Epsilon Alphabet) A) :=
  fun w a =>
     let split := {left := [], right := w, concatEq := by simp}
     let eps := EpsilonIntro Alphabet (Eq.refl [])
     ⟨split, eps, a⟩

def TensorIn {A B C D : SemGrammar Alphabet} :
Reduction Alphabet A B → Reduction Alphabet C D →
  Reduction Alphabet (Tensor Alphabet A C) (Tensor Alphabet B D) :=
  fun f g _ ⟨s , a , c⟩ => ⟨s, f s.left a, g s.right c⟩

def TensorAssoc {A B C : SemGrammar Alphabet} :
  Reduction Alphabet (Tensor Alphabet (Tensor Alphabet A B) C) (Tensor Alphabet A (Tensor Alphabet B C)) :=
  fun _ ⟨s, ⟨s' , a , b⟩ , c⟩ =>
  let split := {left := s'.left, right := s'.right ++ s.right, concatEq := by rw [← List.append_assoc]; rw [s'.concatEq]; rw [s.concatEq]}
  let split' := {left := s'.right, right := s.right, concatEq := by tauto}
  ⟨split, a, ⟨split', b , c⟩⟩

def TensorAssocInv {A B C : SemGrammar Alphabet} :
  Reduction Alphabet (Tensor Alphabet A (Tensor Alphabet B C)) (Tensor Alphabet (Tensor Alphabet A B) C) :=
  fun _ ⟨s, a , ⟨s' , b , c⟩⟩ =>
  let split := {left := s.left ++ s'.left, right := s'.right, concatEq := by simp; rw [s'.concatEq]; rw [s.concatEq]}
  let split' := {left := s.left, right := s'.left, concatEq := by tauto}
  ⟨split, ⟨split', a, b⟩, c⟩

instance : MonoidalCategory (SemGrammar Alphabet) where
  tensorObj := Tensor Alphabet
  whiskerLeft A B C f _ := fun ⟨s , a , b⟩ => ⟨s , a, f _ b⟩
  whiskerRight {A} {B} f C _ := fun ⟨s , a , c⟩ => ⟨s , f _ a , c⟩
  tensorUnit := Epsilon Alphabet
  associator A B C := {
    hom := TensorAssoc Alphabet,
    inv := TensorAssocInv Alphabet,
    hom_inv_id := by funext _ ⟨s, ⟨s' , a , b⟩, c⟩; sorry;
    inv_hom_id := sorry
  }
  leftUnitor A := {
    hom := EpsilonUnitL Alphabet
    inv := EpsilonUnitLInv Alphabet
    hom_inv_id := by
      funext w ⟨s, ⟨⟨nil⟩⟩ , a⟩
      unfold CategoryStruct.comp EpsilonUnitL EpsilonUnitLInv EpsilonIntro CategoryStruct.id instCategorySemGrammar pi
      simp
      sorry
    inv_hom_id := sorry
  }
  rightUnitor A := {
    hom := EpsilonUnitR Alphabet
    inv := EpsilonUnitRInv Alphabet
    hom_inv_id := sorry
    inv_hom_id := sorry
  }
