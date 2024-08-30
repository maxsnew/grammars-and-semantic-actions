open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module Semantics.NFA.Regex.StrongEquivalence
  ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.RegularExpression (Σ₀ , isSetΣ₀)

open import Semantics.NFA.Base (Σ₀ , isSetΣ₀)

open import Semantics.Term (Σ₀ , isSetΣ₀)

open import Semantics.NFA.Regex.Combinators ((Σ₀ , isSetΣ₀))

open RegularExpression
open NFA

regex→NFA : RegularExpression → NFA
regex→NFA ε-Reg = εNFA
regex→NFA ⊥-Reg = emptyNFA
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
    (star-strong-equiv (regex≅NFA r))
