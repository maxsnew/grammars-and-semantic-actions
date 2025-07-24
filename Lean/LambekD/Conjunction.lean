import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import LambekD.Grammar

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

open Limits

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------
@[simp]
def Conjunction {X : Type u} (A : X → SemGrammar.{u}) : SemGrammar :=
 fun (w : SemString ) => (x : X) → A x w

@[simp]
def ConjunctionIn {X : Type u} {A : SemGrammar} {B : X → SemGrammar }
 (f : (x : X) → A ⟶ B x) : A ⟶ Conjunction B :=
 fun (w : SemString ) (a : A w) (x : X) => f x w a

@[simp]
def ConjunctionElim {X : Type u} {A : X → SemGrammar} (x : X) : Conjunction A ⟶ A x :=
 fun (w : SemString ) (f : (Conjunction A) w) => f x

@[simp]
def ConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : Cone F where
 pt := Conjunction (F.obj ∘ Discrete.mk)
 π := {
  app j := ConjunctionElim (Discrete.as j),
  naturality j j' f := by
   funext w a
   unfold CategoryStruct.comp pi
   have jeq : j.as = j'.as := Discrete.eq_of_hom f
   aesop_cat
 }

@[simp]
def ConeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar) : Conjunction F.obj ⟶ (ConeOf F).pt :=
   fun _ f j => f (Discrete.mk j)

@[simp]
def ConeOfIsLimit {J : Type u} (F : Discrete J ⥤ SemGrammar) : IsLimit (ConeOf F) where
  lift (s : Cone F) w a := ConeOfReduction F w (ConjunctionIn s.π.app w a)
  fac s j := by tauto
  uniq := by
   intros s m f
   funext w a j
   unfold ConeOfReduction ConjunctionIn
   simp
   unfold ConeOf at m
   simp at m
   have p : m ≫ (ConeOf F).π.app (Discrete.mk j) = s.π.app (Discrete.mk j) := f (Discrete.mk j)
   have q : (m ≫ (ConeOf F).π.app (Discrete.mk j)) w a = (s.π.app (Discrete.mk j)) w a := congr_fun₂ p w a
   exact q

@[simp]
def LimitConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : LimitCone F where
 cone := ConeOf F
 isLimit := ConeOfIsLimit F

instance : HasProducts.{u} (SemGrammar.{u}) := fun _ =>
 {has_limit F := {exists_limit := Nonempty.intro (LimitConeOf F)}}

@[simp]
def TerminalCone (F : Discrete PEmpty.{1} ⥤ SemGrammar) : Cone F where
  pt := Conjunction (X := PEmpty) (fun x => PEmpty.elim x)
  π := {
    app j := PEmpty.elim (Discrete.as j)
    naturality j := PEmpty.elim (Discrete.as j)
  }

@[simp]
def TerminalConeIsLimit (F : Discrete PEmpty.{1} ⥤ SemGrammar) : IsLimit (TerminalCone F) where
  lift s w _ x := PEmpty.elim x
  fac s j := PEmpty.elim (Discrete.as j)
  uniq s m j := by funext w a x; exact PEmpty.elim x

@[simp]
def TerminalLimitCone (F : Discrete PEmpty.{1} ⥤ SemGrammar) : LimitCone F where
  cone := TerminalCone F
  isLimit := TerminalConeIsLimit F

instance : HasTerminal SemGrammar where
 has_limit F := {exists_limit := Nonempty.intro (TerminalLimitCone F)}

def Terminal : SemGrammar := ⊤_ SemGrammar
