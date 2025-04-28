{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.BinopsAsPrimitive (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Product.Binary.AsPrimitive Alphabet isSetAlphabet public
open import Grammar.Sum.Binary.AsPrimitive Alphabet isSetAlphabet public
