module Cubical.Data.Bool.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

-- TODO could use a better name
-- This also may be derivable with the current Boolean library
--
-- I made this because I often
-- need some middle ground between elim and if_then_else
module _ {ℓA : Level} {A : Type ℓA} where
  if'_then_else_ :
    (b : Bool) →
    (b ≡ true → A) →
    (b ≡ false → A) →
    A
  if' true then x else y = x refl
  if' false then x else y = y refl

or-false :
  ∀ {b} →
  b or false Eq.≡ b
or-false {b = false} = Eq.refl
or-false {b = true} = Eq.refl
