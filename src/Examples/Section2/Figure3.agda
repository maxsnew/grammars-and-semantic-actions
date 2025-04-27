{-# OPTIONS --erased-cubical #-}
module Examples.Section2.Figure3 where

open import Examples.Section2.Alphabet
open import Cubical.Data.Nat
open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.AsEquality.Base Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

g : ＂ a ＂ ⊗ ＂ b ＂ ⊢ (＂ a ＂ *) ⊗ ＂ b ＂ ⊕ ＂ c ＂
g = inl ∘g (CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
import Agda.Builtin.String as BuiltinString

postulate putStrLn : BuiltinString.String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

test : Alphabet → ℕ
test a = zero
test b = suc zero
test c = suc (suc zero)

showNat : ℕ → BuiltinString.String
showNat zero = "0"
showNat 1 = "one"
showNat 2 = "2"
showNat (suc (suc (suc n))) = "big"

main : IO ⊤
main = putStrLn (showNat (test b))
