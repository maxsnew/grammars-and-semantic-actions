open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module NFA.Regex.StrongEquivalence
  (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.RegularExpression Alphabet

open import NFA.Base Alphabet

open import Term Alphabet

open import NFA.Regex.Combinators Alphabet

open RegularExpression
open NFA
open NFA.Accepting

regex→NFA : RegularExpression → NFA ℓ-zero
regex→NFA ε-Reg = εNFA
regex→NFA ⊥-Reg = ⊥NFA
regex→NFA (r ⊗Reg r') = ⊗NFA (regex→NFA r) (regex→NFA r')
regex→NFA (literalReg c) = literalNFA c
regex→NFA (r ⊕Reg r') = ⊕NFA (regex→NFA r) (regex→NFA r')
regex→NFA (KL*Reg r) = *NFA (regex→NFA r)

open StrongEquivalence
regex≅NFA : (r : RegularExpression) →
  StrongEquivalence
    (Parse (regex→NFA r))
    (RegularExpression→Grammar r)
regex≅NFA ε-Reg = εNFA≅
regex≅NFA ⊥-Reg = ⊥NFA≅
regex≅NFA (r ⊗Reg r') =
  comp-strong-equiv
    (⊗NFA≅ _ _)
    (concat-strong-equiv (regex≅NFA r) (regex≅NFA r'))
regex≅NFA (literalReg c) = litNFA≅ c
regex≅NFA (r ⊕Reg r') =
  comp-strong-equiv
    (⊕NFA≅ _ _)
    (disjunct-strong-equiv (regex≅NFA r) (regex≅NFA r'))
regex≅NFA (KL*Reg r) =
  comp-strong-equiv
    (*NFA≅ (regex→NFA r))
    (star-strong-equiv (regex≅NFA r))
