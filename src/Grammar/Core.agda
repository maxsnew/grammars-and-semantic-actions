{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Core (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet public
open import Grammar.Equivalence.Base Alphabet isSetAlphabet public
open import Grammar.Properties Alphabet isSetAlphabet public
open import Grammar.Bottom Alphabet isSetAlphabet public
open import Grammar.Epsilon Alphabet isSetAlphabet public
open import Grammar.Function Alphabet isSetAlphabet public
open import Grammar.Inductive Alphabet isSetAlphabet public
open import Grammar.KleeneStar.Inductive Alphabet isSetAlphabet public
open import Grammar.Lift Alphabet isSetAlphabet public
open import Grammar.LinearFunction Alphabet isSetAlphabet public
open import Grammar.LinearProduct Alphabet isSetAlphabet public
open import Grammar.Literal Alphabet isSetAlphabet public
open import Grammar.Negation Alphabet isSetAlphabet public
open import Grammar.Product Alphabet isSetAlphabet public
open import Grammar.Sum Alphabet isSetAlphabet public
open import Grammar.Top Alphabet isSetAlphabet public
open import Grammar.String Alphabet isSetAlphabet public
open import Grammar.Distributivity Alphabet isSetAlphabet public
open import Grammar.RegularExpression Alphabet isSetAlphabet public
open import Grammar.Equalizer Alphabet isSetAlphabet public
open import Grammar.HLevels Alphabet isSetAlphabet public hiding (⟨_⟩)
