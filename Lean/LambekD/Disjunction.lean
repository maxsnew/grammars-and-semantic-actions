import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import LambekD.Grammar

universe u
variable [AlphabetStr]
open AlphabetStr
open CategoryTheory

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------
open Limits

@[simp]
def Disjunction {X : Type u} (A : X → SemGrammar) : SemGrammar :=
 fun (w : SemString ) => Σ (x : X), A x w

@[simp]
def DisjunctionIn {X : Type u} {A : X → SemGrammar} (x : X) : A x ⟶ Disjunction A :=
 fun (w : SemString ) (a : A x w) => ⟨x , a⟩

@[simp]
def DisjunctionElim {X : Type u} {A : SemGrammar} {B : X → SemGrammar}
 (f : (x : X) → B x ⟶ A) : Disjunction B ⟶ A := fun (w : SemString ) ⟨x , b⟩ => f x w b

@[simp]
def CoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : Cocone F where
 pt := Disjunction (F.obj ∘ Discrete.mk)
 ι := {
  app j w a := DisjunctionIn (Discrete.as j) w a
  naturality j j' f := by
   funext w a
   unfold CategoryStruct.comp pi
   have jeq : j.as = j'.as := Discrete.eq_of_hom f
   aesop_cat
  }

@[simp]
def CoconeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar ) : (CoconeOf F).pt ⟶ Disjunction F.obj :=
   fun _ a => ⟨Discrete.mk a.fst, a.snd⟩

@[simp]
def CoconeOfIsColimit {J : Type u} (F : Discrete J ⥤ SemGrammar) : IsColimit (CoconeOf F) where
  desc (s : Cocone F) w a := DisjunctionElim (fun j => s.ι.app j) w (CoconeOfReduction F w a)
  -- Discrete properties should make this trivial
  fac s j := by tauto -- nice
  uniq := by
   intros s m f
   funext w a
   have p : (CoconeOf F).ι.app { as := a.fst } ≫ m = s.ι.app { as := a.fst } := f (Discrete.mk a.fst)
   have q : ((CoconeOf F).ι.app { as := a.fst } ≫ m) w a.snd = s.ι.app { as := a.fst } w a.snd :=
    congr_fun (congr_fun p w) a.snd
   exact q

@[simp]
def ColimitCoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : ColimitCocone F where
 cocone := CoconeOf F
 isColimit := CoconeOfIsColimit F

instance : HasCoproducts.{u} (SemGrammar.{u}) := fun _ =>
 {has_colimit F := {exists_colimit := Nonempty.intro (ColimitCoconeOf F)}}

@[simp]
def InitialCocone (F : Discrete PEmpty.{1} ⥤ SemGrammar) : Cocone F where
  pt := Disjunction (X := PEmpty) (fun x => PEmpty.elim x)
  ι := {
    app j := PEmpty.elim (Discrete.as j)
    naturality j := PEmpty.elim (Discrete.as j)
  }

@[simp]
def InitialCoconeIsColimit (F : Discrete PEmpty.{1} ⥤ SemGrammar) : IsColimit (InitialCocone F) where
  desc s w a := by simp at a; exact PEmpty.elim a.fst
  fac s j := PEmpty.elim (Discrete.as j)
  uniq s m j := by funext w a; simp at a; exact PEmpty.elim a.fst

@[simp]
def InitialColimitCocone (F : Discrete PEmpty.{1} ⥤ SemGrammar) : ColimitCocone F where
  cocone := InitialCocone F
  isColimit := InitialCoconeIsColimit F

-- Do I want a universe polymorhpic version of this?
instance : HasInitial SemGrammar.{0} where
 has_colimit F := {exists_colimit := Nonempty.intro (InitialColimitCocone F)}

def Initial : SemGrammar := ⊥_ SemGrammar

@[simp]
def BinaryIndexedGrammar (A B : SemGrammar) : Bool → SemGrammar :=
 fun b => match b with
 | true => A
 | false => B

@[simp]
def BinaryDisjunction (A B : SemGrammar) : SemGrammar :=
 Disjunction (X := ULift Bool) (BinaryIndexedGrammar A B ∘ ULift.down)
