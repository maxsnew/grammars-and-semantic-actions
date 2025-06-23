{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck.Grammar where

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

open import Examples.Dyck.Alphabet

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Inductive.Liftless.Indexed Alphabet
open import Grammar.Inductive.Liftless.Structure Alphabet

private
  variable
    ℓ ℓ' : Level

module _ where
  data DyckTag : Type ℓ-zero where
    nil' balanced' : DyckTag

  isSetDyckTag : isSet DyckTag
  isSetDyckTag = isSetRetract enc dec retr isSetBool where
    enc : DyckTag → Bool
    enc nil' = false
    enc balanced' = true
    dec : Bool → DyckTag
    dec false = nil'
    dec true = balanced'
    retr : (x : DyckTag) → dec (enc x) ≡ x
    retr nil' = refl
    retr balanced' = refl

  -- | data Dyck (x : Unit) : L where
  -- |   nil : ↑ Dyck x
  -- |   balanced : ↑ (literal LP ⊗ Dyck x ⊗ literal RP ⊗ Dyck x)
  DyckF : Unit → Functor Unit
  DyckF _ = ⊕e DyckTag (λ
    { nil' → k ε
    ; balanced' → (k (literal [)) ⊗e (Var _) ⊗e (k (literal ]) ⊗e (Var _)) })

  DyckStr : Structure ℓ-zero
  DyckStr = mkStructure DyckF
