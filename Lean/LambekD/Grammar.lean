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

abbrev SemGrammar := SemString.{u} → Type v
