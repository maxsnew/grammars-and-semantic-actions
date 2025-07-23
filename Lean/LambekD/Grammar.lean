import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Iso

universe u v
class AlphabetStr where
 Alphabet : Type u
 readLit : String → Alphabet
 instInahbited : Inhabited Alphabet
 instDecEq : DecidableEq Alphabet

variable [AlphabetStr]
open AlphabetStr

open CategoryTheory
open Category
open CategoryStruct
open Quiver

abbrev SemString := List Alphabet

def StringCat := CategoryTheory.Discrete SemString

def SemGrammar := SemString.{u} → Type (u + 1)

def SemGrammarFunctor := (Discrete SemString.{u} ⥤ (Type (u + 1)))

instance SemGrammarCategory : Category SemGrammar.{u} := pi (I := SemString) _

def Reduction (A B : SemGrammar.{u}) := (w : SemString) → A w → B w

infixr:80 " ⊢ " => Quiver.Hom

def constFamily : SemString.{u} → Type (u + 1) := fun _ => Type u

def FamilyOfTypes : (w : SemString.{u}) → Category (constFamily w) := fun _ => CategoryTheory.types

def IdReduction {A : SemGrammar.{u}} : Reduction A A := fun _ a => a

def IdReduction' {A : SemGrammar.{u}} : A ⊢ A := id A
-- TODO make all reductions morphisms in the grammar category
