open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.DecPropGrammar (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Bottom Alphabet

private
  variable
    ℓG ℓS : Level

DecProp-grammar' :
  DecProp ℓS → Grammar (ℓ-max ℓS ℓG)
DecProp-grammar' d =
  decRec
    (λ _ → ⊤-grammar)
    (λ _ → ⊥*-grammar) (d .snd)
