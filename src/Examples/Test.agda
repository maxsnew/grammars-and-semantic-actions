{-# OPTIONS --erasure --erased-cubical #-}
module Examples.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
import Agda.Builtin.String as BuiltinString

postulate
  putStrLn : BuiltinString.String → IO ⊤
  showNat : ℕ → BuiltinString.String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC showNat = Text.pack . show #-}

f : ℕ → ℕ
f zero = zero
f (suc zero) = zero
f (suc (suc n)) = f n

@0 is-zero : ∀ n → f n ≡ 0
is-zero zero = refl
is-zero (suc zero) = refl
is-zero (suc (suc n)) = is-zero n

main : IO ⊤
main = putStrLn (showNat (suc (f (suc zero))))
