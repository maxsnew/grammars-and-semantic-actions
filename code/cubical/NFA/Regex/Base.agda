open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

module NFA.Regex.Base
  (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.RegularExpression Alphabet
open import Term Alphabet
open import Helper

open import NFA.Base Alphabet
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

isFinOrdStates : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .Q ⟩
isFinOrdStates ε-Reg = isFinOrdUnit
isFinOrdStates ⊥-Reg = isFinOrdUnit
isFinOrdStates (r RegularExpression.⊗Reg r') =
  isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')
isFinOrdStates (literalReg c) =
  EquivPresIsFinOrd
    (invEquiv (isoToEquiv (STATE≅Fin2 c)))
    (isFinOrd⊎ _ isFinOrdUnit _ (isFinOrd⊎ _ isFinOrdUnit _ isFinOrd⊥))
isFinOrdStates (r RegularExpression.⊕Reg r') =
  EquivPresIsFinOrd
    (invEquiv (⊕State-rep (regex→NFA r) (regex→NFA r')))
    (isFinOrd⊎ _ isFinOrdUnit _
      (isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')))
isFinOrdStates (KL*Reg r) =
  isFinOrd⊎ _ isFinOrdUnit _ (isFinOrdStates r)

isFinOrdTransition : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .transition ⟩
isFinOrdTransition ε-Reg = isFinOrd⊥
isFinOrdTransition ⊥-Reg = isFinOrd⊥
isFinOrdTransition (r RegularExpression.⊗Reg r') =
  isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
isFinOrdTransition (literalReg c) = isFinOrdUnit
isFinOrdTransition (r RegularExpression.⊕Reg r') =
  isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
isFinOrdTransition (KL*Reg r) = isFinOrdTransition r

isFinOrdεTransition : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .ε-transition ⟩
isFinOrdεTransition ε-Reg = isFinOrd⊥
isFinOrdεTransition ⊥-Reg = isFinOrd⊥
isFinOrdεTransition (r RegularExpression.⊗Reg r') =
  EquivPresIsFinOrd
    (⊗εTrans-rep (regex→NFA r) (regex→NFA r'))
    (isFinOrd⊎ _
      (isFinOrdΣ ⟨ (regex→NFA r) .Q ⟩
      (isFinOrdStates r)
      _
      (λ q → DecProp→isFinOrd
        (isFinSet→DecProp-Eq≡
          isFinSetBool
          true
          ((regex→NFA r) .isAcc q)
        ))
        )
      _  (isFinOrd⊎ _ (isFinOrdεTransition r)
                    _ (isFinOrdεTransition r')))
isFinOrdεTransition (literalReg c) = isFinOrd⊥
isFinOrdεTransition (r RegularExpression.⊕Reg r') =
  EquivPresIsFinOrd
    (⊕εTrans-rep (regex→NFA r) (regex→NFA r'))
    (isFinOrd⊎
      _ isFinOrdUnit
      _ (isFinOrd⊎ _ isFinOrdUnit _
        (isFinOrd⊎ _ (isFinOrdεTransition r) _ (isFinOrdεTransition r')))
      )
isFinOrdεTransition (KL*Reg r) =
  EquivPresIsFinOrd
    (*εTrans-rep (regex→NFA r))
    (isFinOrd⊎ _ isFinOrdUnit _
      (isFinOrd⊎ _
        (isFinOrdΣ _ (isFinOrdStates r) _
        (λ q → DecProp→isFinOrd
          (isFinSet→DecProp-Eq≡
            isFinSetBool
            true
            ((regex→NFA r) .isAcc q)
          ))
        )
        _ (isFinOrdεTransition r)))

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
