{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Lift (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

LiftG : ∀ ℓ' → Grammar ℓ → Grammar (ℓ-max ℓ ℓ')
LiftG ℓ' g w = Lift {j = ℓ'} (g w)

liftG : g ⊢ LiftG ℓ' g
liftG = λ w z → lift z

lowerG : LiftG ℓ' g ⊢ g
lowerG = λ w z → z .lower
