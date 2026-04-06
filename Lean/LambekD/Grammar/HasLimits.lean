import LambekD.Grammar.Cat
import LambekD.Grammar.Product
import LambekD.Grammar.Sum
import LambekD.Grammar.Top
import LambekD.Grammar.Bottom

import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Limits and colimits for Grammar

Products, coproducts, terminal, and initial objects in the category of grammars,
using `IdxProduct`, `IdxCoproduct`, `Top`, and `Bottom` from the core definitions.
-/

namespace LambekD

universe u

open CategoryTheory Limits
variable {Alphabet : Type u}

-- ════════════════════════════════════════════════════════════
-- Products
-- ════════════════════════════════════════════════════════════

/-- The cone for a discrete diagram given by indexed conjunction. -/
def productCone {J : Type u} (F : Discrete J ⥤ Grammar.{u, u} Alphabet) : Cone F where
  pt := IdxProduct J (F.obj ∘ Discrete.mk)
  π := {
    app j := fun w f => f (Discrete.as j)
    naturality j j' g := by
      have jeq : j.as = j'.as := Discrete.eq_of_hom g
      aesop_cat
  }

/-- The product cone is a limit. -/
def productConeIsLimit {J : Type u} (F : Discrete J ⥤ Grammar.{u, u} Alphabet) :
    IsLimit (productCone F) where
  lift s w a j := s.π.app (Discrete.mk j) w a
  fac _ _ := rfl
  uniq s m h := by
    funext w a j
    exact congr_fun₂ (h (Discrete.mk j)) w a

instance : HasProducts.{u} (Grammar.{u, u} Alphabet) := fun _ =>
  { has_limit := fun F => ⟨⟨productCone F, productConeIsLimit F⟩⟩ }

-- ════════════════════════════════════════════════════════════
-- Terminal
-- ════════════════════════════════════════════════════════════

/-- Cone for the empty diagram, whose point is `Top`. -/
def terminalCone (F : Discrete PEmpty.{1} ⥤ Grammar.{u, u} Alphabet) : Cone F where
  pt := Top
  π := {
    app j := PEmpty.elim (Discrete.as j)
    naturality j := PEmpty.elim (Discrete.as j)
  }

/-- The terminal cone is a limit. -/
def terminalConeIsLimit (F : Discrete PEmpty.{1} ⥤ Grammar.{u, u} Alphabet) :
    IsLimit (terminalCone F) where
  lift _ := topIntro _
  fac _ j := PEmpty.elim (Discrete.as j)
  uniq _ m _ := top_η m (topIntro _)

instance : HasTerminal (Grammar.{u, u} Alphabet) where
  has_limit F := ⟨⟨terminalCone F, terminalConeIsLimit F⟩⟩

-- ════════════════════════════════════════════════════════════
-- Coproducts
-- ════════════════════════════════════════════════════════════

/-- The cocone for a discrete diagram given by indexed disjunction. -/
def coproductCocone {J : Type u} (F : Discrete J ⥤ Grammar.{u, u} Alphabet) : Cocone F where
  pt := IdxCoproduct J (F.obj ∘ Discrete.mk)
  ι := {
    app j w a := ⟨Discrete.as j, a⟩
    naturality j j' g := by
      have jeq : j.as = j'.as := Discrete.eq_of_hom g
      aesop_cat
  }

/-- The coproduct cocone is a colimit. -/
def coproductCoconeIsColimit {J : Type u} (F : Discrete J ⥤ Grammar.{u, u} Alphabet) :
    IsColimit (coproductCocone F) where
  desc s w x := s.ι.app (Discrete.mk x.1) w x.2
  fac _ _ := rfl
  uniq s m h := by
    funext w ⟨j, a⟩
    exact congr_fun₂ (h (Discrete.mk j)) w a

instance : HasCoproducts.{u} (Grammar.{u, u} Alphabet) := fun _ =>
  { has_colimit := fun F => ⟨⟨coproductCocone F, coproductCoconeIsColimit F⟩⟩ }

-- ════════════════════════════════════════════════════════════
-- Initial
-- ════════════════════════════════════════════════════════════

/-- Cocone for the empty diagram, whose point is `Bottom`. -/
def initialCocone (F : Discrete PEmpty.{1} ⥤ Grammar.{u, u} Alphabet) : Cocone F where
  pt := Bottom
  ι := {
    app j := PEmpty.elim (Discrete.as j)
    naturality j := PEmpty.elim (Discrete.as j)
  }

/-- The initial cocone is a colimit. -/
def initialCoconeIsColimit (F : Discrete PEmpty.{1} ⥤ Grammar.{u, u} Alphabet) :
    IsColimit (initialCocone F) where
  desc s := botElim _
  fac _ j := PEmpty.elim (Discrete.as j)
  uniq _ m _ := bot_η m (botElim _)

instance : HasInitial (Grammar.{u, u} Alphabet) where
  has_colimit F := ⟨⟨initialCocone F, initialCoconeIsColimit F⟩⟩

end LambekD
