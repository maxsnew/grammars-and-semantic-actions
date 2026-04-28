open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Unfold (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Epsilon.AsEquality.Properties Alphabet
open import Grammar.Literal.AsEquality.Base Alphabet
open import Grammar.LinearProduct.AsEquality.Properties Alphabet
open import Grammar.LinearFunction.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Properties Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet
open import Grammar.Function.AsPrimitive.Base Alphabet
open import Grammar.Top.Properties Alphabet
open import Grammar.Bottom.Properties Alphabet
open import Grammar.KleeneStar.Inductive.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.External.String.Tiny Alphabet

opaque
  unfolding unfoldEpsilonDefs
            unfoldLiteralDefs
            unfoldLinearProductDefs
            unfoldLinearFunctionDefs
            unfoldSumBinaryDefs
            unfoldSumIndexedDefs
            unfoldProductBinaryDefs
            unfoldFunctionDefs
            unfoldTopDefs
            unfoldBottomDefs
            unfoldKleeneStarDefs
            unfoldStringDefs
            unfoldTinyDefs
  unfoldGrammarDefs : Unit
  unfoldGrammarDefs = tt
