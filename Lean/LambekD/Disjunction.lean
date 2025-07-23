import Mathlib.CategoryTheory.Limits.Shapes.Products
import LambekD.Grammar

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------
open Limits

def Disjunction {X : Type u} (A : X → SemGrammar.{u}) : SemGrammar :=
 fun (w : SemString ) => Σ (x : X), A x w

def DisjunctionIn {X : Type u} {A : X → SemGrammar.{u}} (x : X) : Reduction (A x) (Disjunction A) :=
 fun (w : SemString ) (a : A x w) => ⟨x , a⟩

def DisjunctionElim {X : Type u} {A : SemGrammar} {B : X → SemGrammar }
 (f : (x : X) → Reduction (B x) A) : Reduction (Disjunction B) A :=
 fun (w : SemString ) ⟨x , b⟩ => f x w b

def CoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : Cocone F where
 pt := Disjunction (F.obj ∘ Discrete.mk)
 ι := {
  app j w a := DisjunctionIn (Discrete.as j) w a
  naturality j j' f := by
   funext w a
   unfold CategoryStruct.comp instCategorySemGrammar pi
   have jeq : j.as = j'.as := Discrete.eq_of_hom f
   aesop_cat
  }

def CoconeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar ) :
  Reduction (CoconeOf F).pt (Disjunction F.obj) :=
   fun _ a => ⟨Discrete.mk a.fst, a.snd⟩

def CoconeOfIsColimit {J : Type u} (F : Discrete J ⥤ SemGrammar ) : IsColimit (CoconeOf F) where
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

def ColimitCoconeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : ColimitCocone F where
 cocone := CoconeOf F
 isColimit := CoconeOfIsColimit F

instance : HasCoproducts.{u} (SemGrammar.{u}) := fun _ =>
 {has_colimit F := {exists_colimit := Nonempty.intro (ColimitCoconeOf F)}}

def Initial : SemGrammar := Disjunction (X := PEmpty) (fun x => PEmpty.elim x)

def InitialElim {A : SemGrammar} : Reduction (Initial ) A :=
 fun w x => by
  unfold Initial Disjunction at x
  exact (PEmpty.elim (x.fst))

def BinaryIndexedGrammar (A B : SemGrammar) : Bool → SemGrammar :=
 fun b => match b with
 | true => A
 | false => B

def BinaryDisjunction (A B : SemGrammar) : SemGrammar :=
 Disjunction (X := ULift Bool) (BinaryIndexedGrammar A B ∘ ULift.down)
