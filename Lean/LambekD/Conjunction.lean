import Mathlib.CategoryTheory.Limits.Shapes.Products
import LambekD.Grammar

universe u v
variable [AlphabetStr.{u}]
open AlphabetStr
open CategoryTheory

open Limits

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------
def Conjunction {X : Type u} (A : X → SemGrammar.{u}) : SemGrammar :=
 fun (w : SemString ) => (x : X) → A x w

def ConjunctionIn {X : Type u} {A : SemGrammar} {B : X → SemGrammar }
 (f : (x : X) → Reduction A (B x)) : Reduction A (Conjunction B) :=
 fun (w : SemString ) (a : A w) (x : X) => f x w a

def ConjunctionElim {X : Type u} {A : X → SemGrammar} (x : X) : Reduction (Conjunction A) (A x) :=
 fun (w : SemString ) (f : (Conjunction A) w) => f x

def ConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar) : Cone F where
 pt := Conjunction (F.obj ∘ Discrete.mk)
 π := {
  app j := ConjunctionElim (Discrete.as j),
  naturality j j' f := by
   funext w a
   unfold CategoryStruct.comp instCategorySemGrammar pi
   have jeq : j.as = j'.as := Discrete.eq_of_hom f
   aesop_cat
 }

def ConeOfReduction {J : Type u} (F : Discrete J ⥤ SemGrammar) :
  Reduction (Conjunction F.obj) (ConeOf F).pt :=
   fun _ f j => f (Discrete.mk j)

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

def LimitConeOf {J : Type u} (F : Discrete J ⥤ SemGrammar ) : LimitCone F where
 cone := ConeOf F
 isLimit := ConeOfIsLimit F

instance : HasProducts.{u} (SemGrammar.{u}) := fun _ =>
 {has_limit F := {exists_limit := Nonempty.intro (LimitConeOf F)}}

def Terminal : SemGrammar := Conjunction (X := PEmpty) (fun x => PEmpty.elim x)

def TerminalIn {A : SemGrammar} : Reduction A Terminal :=
 fun _ _ x => PEmpty.elim x
