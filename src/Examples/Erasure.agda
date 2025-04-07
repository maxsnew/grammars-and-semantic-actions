module Examples.Erasure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

f : ℕ → (ℕ ≡ ℕ) → ℕ
f a pathAB = transport pathAB a

main : ℕ
main = f 0 refl
