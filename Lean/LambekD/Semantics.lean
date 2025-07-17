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
import Canonical

import Lean

open Lean Elab Tactic

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

@[ext]
def Splitting.ext {w : SemString Alphabet} {s s' : Splitting Alphabet w} :
   s.left = s'.left → s.right = s'.right → s = s' := by
  intro hl hr
  cases s with
  | mk left right concatEq =>
    cases s' with
    | mk left' right' concatEq' =>
       simp at hl hr
       subst hl hr
       rfl

structure TensorTy (A B : SemGrammar Alphabet) (w : SemString Alphabet) where
  split : Splitting Alphabet w
  left : A (split.left)
  right : B (split.right)


def Tensor (A B : SemGrammar Alphabet) : SemGrammar Alphabet := λ (w : SemString Alphabet) => TensorTy Alphabet A B w

@[ext]
def Tensor.ext {w : SemString Alphabet} {A B : SemGrammar Alphabet} {ab ab' : Tensor Alphabet A B w} :
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

def SemLiteral (c : Alphabet) : SemGrammar Alphabet := λ w => ULift (PLift (w = [ c ]))

def LiteralIntro : {w : SemString Alphabet} → {c : Alphabet} → (w = [ c ]) → SemLiteral Alphabet c w :=
  fun p => ULift.up (PLift.up p)

def Epsilon : SemGrammar Alphabet := λ (w : SemString Alphabet) => ULift (PLift (w = List.nil))

def EpsilonIntro : {w : SemString Alphabet} → (w = List.nil) → Epsilon Alphabet w :=
  fun p => ULift.up (PLift.up p)

def EpsilonUnitR : {A : SemGrammar Alphabet} →
  Reduction Alphabet (Tensor Alphabet A (Epsilon Alphabet)) A :=
  fun w ⟨⟨l, r, ce⟩ , a , ⟨⟨nil⟩⟩⟩ =>
    let lw : l = w := by
      simp at nil
      rw [nil] at ce
      simp at ce
      exact ce
    Eq.rec a lw

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

set_option pp.proofs true
instance : MonoidalCategory (SemGrammar Alphabet) where
  tensorObj := Tensor Alphabet
  whiskerLeft A B C f _ := fun ⟨s , a , b⟩ => ⟨s , a, f _ b⟩
  whiskerRight {A} {B} f C _ := fun ⟨s , a , c⟩ => ⟨s , f _ a , c⟩
  tensorUnit := Epsilon Alphabet
  associator A B C := {
    hom := TensorAssoc Alphabet,
    inv := TensorAssocInv Alphabet,
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
    hom := EpsilonUnitL Alphabet
    inv := EpsilonUnitLInv Alphabet
    hom_inv_id := by
      funext w ⟨⟨l, r, ce⟩, ⟨⟨nil⟩⟩ , a⟩
      cases ce with | refl => cases nil with | refl => tauto
  }
  leftUnitor_naturality f := by
      funext w ⟨⟨l, r, ce⟩, ⟨⟨nil⟩⟩ , a⟩
      cases ce with | refl => cases nil with | refl => tauto
  rightUnitor A := {
    hom := EpsilonUnitR Alphabet
    inv := EpsilonUnitRInv Alphabet
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
      let x := EpsilonUnitR._proof_1 Alphabet w l r ce nil
      have h : l = w := sorry
      rw [← h] at x
      cases x with | refl =>
        subst h
        rfl
  triangle := sorry
  pentagon := sorry

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------
open Limits

def Disjunction {X : Type u} (A : X → SemGrammar Alphabet) : SemGrammar Alphabet :=
  fun (w : SemString Alphabet) => Σ (x : X), A x w

def DisjunctionIn {X : Type u} {A : X → SemGrammar Alphabet} (x : X) : Reduction Alphabet (A x) (Disjunction Alphabet A) :=
  fun (w : SemString Alphabet) (a : A x w) => ⟨x , a⟩

def DisjunctionElim {X : Type u} {A : SemGrammar Alphabet} {B : X → SemGrammar Alphabet}
  (f : (x : X) → Reduction Alphabet (B x) A) : Reduction Alphabet (Disjunction Alphabet B) A :=
  fun (w : SemString Alphabet) ⟨x , b⟩ => f x w b

def CoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : Cocone F where
  pt := Disjunction Alphabet (F.obj ∘ Discrete.mk)
  ι := {
    app j w a := DisjunctionIn Alphabet (Discrete.as j) w a
    naturality j j' f := by
      funext w a
      unfold CategoryStruct.comp instCategorySemGrammar pi
      have jeq : j.as = j'.as := Discrete.eq_of_hom f
      aesop_cat
    }

def CoconeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) :
   Reduction Alphabet (CoconeOf Alphabet F).pt (Disjunction Alphabet F.obj) :=
      fun _ a => ⟨Discrete.mk a.fst, a.snd⟩

def CoconeOfIsColimit {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : IsColimit (CoconeOf Alphabet F) where
    desc (s : Cocone F) w a := DisjunctionElim Alphabet (fun j => s.ι.app j) w (CoconeOfReduction Alphabet F w a)
    -- Discrete properties should make this trivial
    fac s j := by tauto -- nice
    uniq := by
      intros s m f
      funext w a
      have p : (CoconeOf Alphabet F).ι.app { as := a.fst } ≫ m = s.ι.app { as := a.fst } := f (Discrete.mk a.fst)
      have q : ((CoconeOf Alphabet F).ι.app { as := a.fst } ≫ m) w a.snd = s.ι.app { as := a.fst } w a.snd :=
        congr_fun (congr_fun p w) a.snd
      exact q

def ColimitCoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : ColimitCocone F where
  cocone := CoconeOf Alphabet F
  isColimit := CoconeOfIsColimit Alphabet F

instance : HasCoproducts.{u} (SemGrammar Alphabet) := fun _ =>
  {has_colimit F := {exists_colimit := Nonempty.intro (ColimitCoconeOf Alphabet F)}}

def Initial : SemGrammar Alphabet := Disjunction Alphabet (X := PEmpty) (fun x => PEmpty.elim x)

def InitialElim {A : SemGrammar Alphabet} : Reduction Alphabet (Initial Alphabet) A :=
  fun w x => by
    unfold Initial Disjunction at x
    exact (PEmpty.elim (x.fst))

def BinaryIndexedGrammar (A B : SemGrammar Alphabet) : Bool → SemGrammar Alphabet :=
  fun b => match b with
  | true => A
  | false => B

def BinaryDisjunction (A B : SemGrammar Alphabet) : SemGrammar Alphabet :=
  Disjunction Alphabet (X := ULift Bool) (BinaryIndexedGrammar Alphabet A B ∘ ULift.down)

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

def ConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : Cone F where
  pt := Conjunction Alphabet (F.obj ∘ Discrete.mk)
  π := {
    app j := ConjunctionElim Alphabet (Discrete.as j),
    naturality j j' f := by
      funext w a
      unfold CategoryStruct.comp instCategorySemGrammar pi
      have jeq : j.as = j'.as := Discrete.eq_of_hom f
      aesop_cat
  }

def ConeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) :
   Reduction Alphabet (Conjunction Alphabet F.obj) (ConeOf Alphabet F).pt :=
      fun _ f j => f (Discrete.mk j)

def ConeOfIsLimit {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : IsLimit (ConeOf Alphabet F) where
    lift (s : Cone F) w a := ConeOfReduction Alphabet F w (ConjunctionIn Alphabet s.π.app w a)
    fac s j := by tauto
    uniq :=  by
      intros s m f
      funext w a j
      unfold ConeOfReduction ConjunctionIn
      simp
      unfold ConeOf at m
      simp at m
      have p : m ≫ (ConeOf Alphabet F).π.app (Discrete.mk j) = s.π.app (Discrete.mk j) := f (Discrete.mk j)
      have q : (m ≫ (ConeOf Alphabet F).π.app (Discrete.mk j)) w a = (s.π.app (Discrete.mk j)) w a := congr_fun₂ p w a
      exact q

def LimitConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar Alphabet) : LimitCone F where
  cone := ConeOf Alphabet F
  isLimit := ConeOfIsLimit Alphabet F

instance : HasProducts.{u} (SemGrammar Alphabet) := fun _ =>
  {has_limit F := {exists_limit := Nonempty.intro (LimitConeOf Alphabet F)}}

def Terminal : SemGrammar Alphabet := Conjunction Alphabet (X := PEmpty) (fun x => PEmpty.elim x)

def TerminalIn {A : SemGrammar Alphabet} : Reduction Alphabet A (Terminal Alphabet) :=
  fun _ _ x => PEmpty.elim x

--------------------------------------------------------------------------------
-- Kleene Star
--------------------------------------------------------------------------------
inductive Star (A : SemGrammar Alphabet) : SemGrammar Alphabet where
  | nil : Star A []
  | cons : {w w' : SemString Alphabet} → A w → Star A w' → Star A (w ++ w')
