import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types
-- import Mathlib.CategoryTheory.Limits.HasLimits
-- import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
-- import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Monoidal.Category
-- import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.List.Basic

universe u v
class AlphabetStr where
  Alphabet : Type u
  readLit : String → Alphabet
  instInahbited : Inhabited Alphabet
  instDecEq : DecidableEq Alphabet

variable [AlphabetStr]
variable (Alphabet : Type u)
variable [Inhabited Alphabet]
variable [DecidableEq Alphabet]

open CategoryTheory

abbrev SemString := List Alphabet

def StringCat := CategoryTheory.Discrete (SemString Alphabet)

def SemGrammar := SemString Alphabet → Type (u + 1)

def SemGrammarFunctor := (Discrete (SemString Alphabet) ⥤ (Type (u + 1)))

-- instance SemGrammarFunctorEquivalence :
--   (SemString Alphabet → Type (u + 1)) ≌ (Discrete (SemString Alphabet) ⥤ (Type (u + 1))) :=
--     piEquivalenceFunctorDiscrete _ _

-- open Limits

-- instance SemGrammarFunctorHasColimits : HasColimits (Discrete (SemString Alphabet) ⥤ (Type (u + 1))) :=
--   functorCategoryHasColimitsOfSize

-- instance SemGrammarHasColimits : HasColimits (SemString Alphabet → Type (u + 1)) :=
--   Adjunction.has_colimits_of_equivalence ((SemGrammarFunctorEquivalence Alphabet).functor)

def Reduction (A B : SemGrammar Alphabet) := (w : SemString Alphabet) → A w → B w

def constFamily : SemString Alphabet → Type (u + 1) := fun _ => Type u

def FamilyOfTypes : (w : SemString Alphabet) → Category (constFamily Alphabet w) := fun _ => CategoryTheory.types

instance : Category (SemGrammar Alphabet) := pi (I := SemString Alphabet) _

def IdReduction {A : SemGrammar Alphabet} : Reduction Alphabet A A := fun _ a => a

--------------------------------------------------------------------------------
-- Monoidal Structure
--------------------------------------------------------------------------------
structure Splitting (w : SemString Alphabet) where
  left : SemString Alphabet
  right : SemString Alphabet
  concatEq : left ++ right = w

structure TensorTy (A B : SemGrammar Alphabet) (w : SemString Alphabet) where
  split : Splitting Alphabet w
  left : A (split.left)
  right : B (split.right)

def Tensor (A B : SemGrammar Alphabet) : SemGrammar Alphabet := λ (w : SemString Alphabet) => TensorTy Alphabet A B w

def SemLiteral (c : Alphabet) : SemGrammar Alphabet := λ w => ULift (PLift (w = [ c ]))

def LiteralIntro : {w : SemString Alphabet} → {c : Alphabet} → (w = [ c ]) → SemLiteral Alphabet c w :=
  fun p => ULift.up (PLift.up p)

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
      unfold CategoryStruct.comp EpsilonUnitL EpsilonUnitLInv EpsilonIntro CategoryStruct.id instCategorySemGrammar pi Tensor
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

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------
open Limits

instance : HasCoproducts.{u} (SemGrammar Alphabet) := fun J =>
  {
  has_colimit F :=
    let disj := fun w => Σ (j : J), F.obj (Discrete.mk j) w
    let cocone := {
      pt := disj,
      ι := {
        app j w a := ⟨Discrete.as j , a⟩,
        naturality j j' f := by
          funext w a
          unfold CategoryStruct.comp instCategorySemGrammar pi
          have jeq : j.as = j'.as := Discrete.eq_of_hom f
          aesop_cat
        }
  }
  let isColimit : IsColimit cocone :=
    let descDef s w a :=
      let f := s.ι.app (Discrete.mk a.fst)
      by
      unfold instCategorySemGrammar pi at f
      simp at f
      exact f w (a.snd)
    {
    desc := descDef
    -- Discrete properties should make this trivial
    fac s j := by tauto
    uniq := by
      intros s m f
      unfold descDef
      simp
      funext w a
      have p : cocone.ι.app { as := a.fst } ≫ m = s.ι.app { as := a.fst } := f (Discrete.mk a.fst)
      have q : (cocone.ι.app { as := a.fst } ≫ m) w a.snd = s.ι.app { as := a.fst } w a.snd := congr_fun (congr_fun p w) a.snd
      exact q
  }
  let colim := {cocone := cocone, isColimit := isColimit}
  {exists_colimit := Nonempty.intro colim}
}

-- TODO redefine everything in terms of the above categorical structures
-- The below definition is equivalent to disj in the HasCoproducts term above, but I'm
-- curious if its better to define this as a universal construction, rather than proving
-- that it is universal
-- Need functor comprehension
def Disjunction {X : Type u} (A : X → SemGrammar Alphabet) : SemGrammar Alphabet :=
  fun (w : SemString Alphabet) => Σ (x : X), A x w

def DisjunctionIn {X : Type u} {A : X → SemGrammar Alphabet} (x : X) : Reduction Alphabet (A x) (Disjunction Alphabet A) :=
  fun (w : SemString Alphabet) (a : A x w) => ⟨x , a⟩

def DisjunctionElim {X : Type u} {A : SemGrammar Alphabet} {B : X → SemGrammar Alphabet}
  (f : (x : X) → Reduction Alphabet (B x) A) : Reduction Alphabet (Disjunction Alphabet B) A :=
  fun (w : SemString Alphabet) ⟨x , b⟩ => f x w b

def Initial : SemGrammar Alphabet := Disjunction Alphabet (X := PEmpty) (fun x => PEmpty.elim x)

def InitialElim {A : SemGrammar Alphabet} : Reduction Alphabet (Initial Alphabet) A :=
  fun w x => by
    unfold Initial Disjunction at x
    exact (PEmpty.elim (x.fst))

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------
def Conjunction {X : Type u} (A : X → SemGrammar Alphabet) : SemGrammar Alphabet :=
  fun (w : SemString Alphabet) => (x : X) → A x w

def ConjunctionIn {X : Type u} {A : SemGrammar Alphabet} {B : X → SemGrammar Alphabet}
  (f : (x : X) → Reduction Alphabet A (B x)) : Reduction Alphabet A (Conjunction Alphabet B) :=
  fun (w : SemString Alphabet) (a : A w) (x : X) => f x w a

def ConjunctionElim {X : Type u} {A : X → SemGrammar Alphabet} (x : X) : Reduction Alphabet (Conjunction Alphabet A) (A x) :=
  fun (w : SemString Alphabet) (f : (Conjunction Alphabet A) w) => f x

def Terminal : SemGrammar Alphabet := Conjunction Alphabet (X := PEmpty) (fun x => PEmpty.elim x)

def TerminalIn {A : SemGrammar Alphabet} : Reduction Alphabet A (Terminal Alphabet) :=
  fun _ _ x => PEmpty.elim x

--------------------------------------------------------------------------------
-- Kleene Star
--------------------------------------------------------------------------------
inductive Star (A : SemGrammar Alphabet) : SemGrammar Alphabet where
  | nil : Star A []
  | cons : {w w' : SemString Alphabet} → A w → Star A w' → Star A (w ++ w')
