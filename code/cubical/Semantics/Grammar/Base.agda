open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.String (Σ₀ , isSetΣ₀) public
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable ℓG ℓG' ℓH ℓK ℓL : Level

module _ where
  module _ ℓG where
    Grammar : Type (ℓ-suc ℓG)
    Grammar = String → Type ℓG

  module _ {ℓG}{ℓG'}
    (g : Grammar ℓG)
    where

    LiftGrammar : Grammar (ℓ-max ℓG ℓG')
    LiftGrammar w = Lift {ℓG}{ℓG'} (g w)

