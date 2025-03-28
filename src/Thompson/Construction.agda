-- We constructs NFAs that are strongly equivalent to
-- regular expressions.
--
-- For each constructor of a regular expression, we build
-- a corresponding NFA. And then we inductively combine smaller
-- NFAs into one machine that is equivalent to the regex
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Thompson.Construction (Alphabet : hSet ℓ-zero) where

open import Thompson.Construction.Bottom Alphabet public
open import Thompson.Construction.Epsilon Alphabet public
open import Thompson.Construction.Literal Alphabet public
open import Thompson.Construction.LinearProduct Alphabet public
open import Thompson.Construction.Sum Alphabet public
open import Thompson.Construction.KleeneStar Alphabet public
