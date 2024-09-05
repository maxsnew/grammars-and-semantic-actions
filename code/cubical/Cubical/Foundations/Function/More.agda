module Cubical.Foundations.Function.More where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'

infixl 0 _&_

_&_ : (a : A) → ((a : A) → B a) → B a
a & f = f a
