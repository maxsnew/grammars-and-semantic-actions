{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck.Alphabet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

data Bracket : Type where
  [ ] : Bracket

opaque
  BracketRep : Bracket ≃ Bool
  BracketRep = isoToEquiv (iso
    (λ { [ → true ; ] → false })
    (λ { false → ] ; true → [ })
    (λ { false → refl ; true → refl })
    λ { [ → refl ; ] → refl })

  isFinBracket : isFinSet Bracket
  isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

  isSetBracket : isSet Bracket
  isSetBracket = isFinSet→isSet isFinBracket

Alphabet : hSet _
Alphabet = (Bracket , isSetBracket)

LP = [
RP = ]

