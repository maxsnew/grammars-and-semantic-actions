open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module NFA.Regex.StrongEquivalence
  (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.RegularExpression Alphabet

open import NFA.Manual Alphabet

open import Term Alphabet

open import NFA.Regex.Combinators Alphabet

open RegularExpression
open NFA

regex→NFA : RegularExpression → NFA
regex→NFA ε-Reg = εNFA
regex→NFA ⊥-Reg = ⊥NFA
regex→NFA (r ⊗Reg r') = ⊗NFA (regex→NFA r) (regex→NFA r')
regex→NFA (literalReg c) = literalNFA c
regex→NFA (r ⊕Reg r') = ⊕NFA (regex→NFA r) (regex→NFA r')
regex→NFA (KL*Reg r) = *NFA (regex→NFA r)

open StrongEquivalence
regex≅NFA : (r : RegularExpression) →
  StrongEquivalence
    (InitParse (regex→NFA r))
    (RegularExpression→Grammar r)
regex≅NFA ε-Reg = εNFA-strong-equiv
regex≅NFA ⊥-Reg = emptyNFA-strong-equiv
regex≅NFA (r ⊗Reg r') =
  comp-strong-equiv
    (⊗-strong-equivalence _ _)
    (concat-strong-equiv (regex≅NFA r) (regex≅NFA r'))
regex≅NFA (literalReg c) = litNFA-strong-equiv c
regex≅NFA (r ⊕Reg r') =
  comp-strong-equiv
    (⊕-strong-equivalence _ _)
    (disjunct-strong-equiv (regex≅NFA r) (regex≅NFA r'))
regex≅NFA (KL*Reg r) =
  comp-strong-equiv
    (*-strong-equivalence (regex→NFA r))
    (manual-star-strong-equiv (regex≅NFA r))
