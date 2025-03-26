open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Thompson.Equivalence (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet
open import Thompson.Base Alphabet

open import Automata.NFA.Base Alphabet
open import Thompson.Construction Alphabet

open RegularExpression
open NFA.Accepting

open StrongEquivalence

regex≅NFA : (r : RegularExpression) → Parse (regex→NFA r) ≅ RegularExpression→Grammar r
regex≅NFA εr = εNFA≅
regex≅NFA ⊥r = ⊥NFA≅
regex≅NFA (r ⊗r r') = ⊗NFA≅ _ _ ≅∙ ⊗≅ (regex≅NFA r) (regex≅NFA r')
regex≅NFA (＂ c ＂r) = litNFA≅ c
regex≅NFA (r ⊕r r') = ⊕NFA≅ _ _ ≅∙ ⊕≅ (regex≅NFA r) (regex≅NFA r')
regex≅NFA (r *r) = *NFA≅ (regex→NFA r) ≅∙ *≅ (regex≅NFA r)
