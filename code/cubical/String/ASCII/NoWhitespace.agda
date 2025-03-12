open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.ASCII.NoWhitespace where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More
open import Cubical.Relation.Nullary.DecidablePropositions.Powerset.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding

open import Cubical.Data.SumFin

open import String.ASCII.Base
open import String.SubAlphabet

open DecidablePowerset

NWSubset : Decℙ ASCIIChar
NWSubset c =
  DecProp× (dp c SPACE)
    (DecProp×
      (dp c NEWLINE)
      (dp c TAB))
  where
  dp : ASCIIChar → ASCIIChar → DecProp ℓ-zero
  dp c c' = negateDecProp
    (((c ≡ c') , isSetASCII _ _) , (DiscreteASCII c c'))

NWCharFun : ASCIIChar → Bool
NWCharFun c = DecProp→Bool (NWSubset c)

ASCIINW : hSet ℓ-zero
ASCIINW = SubAlphabet ASCII NWCharFun
