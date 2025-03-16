open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

module Thompson.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.More
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Bool

open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar Alphabet
open import Term Alphabet

open import NFA.Base Alphabet
open import Thompson.Construction Alphabet

open RegularExpression
open NFA
open NFA.Accepting

regex→NFA : RegularExpression → NFA ℓ-zero
regex→NFA εr = εNFA
regex→NFA ⊥r = ⊥NFA
regex→NFA (r ⊗r r') = ⊗NFA (regex→NFA r) (regex→NFA r')
regex→NFA (＂ c ＂r) = literalNFA c
regex→NFA (r ⊕r r') = ⊕NFA (regex→NFA r) (regex→NFA r')
regex→NFA (r *r) = *NFA (regex→NFA r)

isFinOrdStates : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .Q ⟩
isFinOrdStates εr = isFinOrdUnit
isFinOrdStates ⊥r = isFinOrdUnit
isFinOrdStates (r ⊗r r') =
  isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')
isFinOrdStates (＂ c ＂r) =
  EquivPresIsFinOrd
    (invEquiv (isoToEquiv (STATE≅Fin2 c)))
    (isFinOrd⊎ _ isFinOrdUnit _ (isFinOrd⊎ _ isFinOrdUnit _ isFinOrd⊥))
isFinOrdStates (r ⊕r r') =
  EquivPresIsFinOrd
    (invEquiv (⊕State-rep (regex→NFA r) (regex→NFA r')))
    (isFinOrd⊎ _ isFinOrdUnit _
      (isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')))
isFinOrdStates (r *r) =
  isFinOrd⊎ _ isFinOrdUnit _ (isFinOrdStates r)

isFinOrdTransition : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .transition ⟩
isFinOrdTransition εr = isFinOrd⊥
isFinOrdTransition ⊥r = isFinOrd⊥
isFinOrdTransition (r ⊗r r') =
  isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
isFinOrdTransition (＂ c ＂r) = isFinOrdUnit
isFinOrdTransition (r ⊕r r') =
  isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
isFinOrdTransition (r *r) = isFinOrdTransition r

isFinOrdεTransition : (r : RegularExpression) → isFinOrd ⟨ regex→NFA r .ε-transition ⟩
isFinOrdεTransition εr = isFinOrd⊥
isFinOrdεTransition ⊥r = isFinOrd⊥
isFinOrdεTransition (r ⊗r r') =
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
isFinOrdεTransition (＂ c ＂r) = isFinOrd⊥
isFinOrdεTransition (r ⊕r r') =
  EquivPresIsFinOrd
    (⊕εTrans-rep (regex→NFA r) (regex→NFA r'))
    (isFinOrd⊎
      _ isFinOrdUnit
      _ (isFinOrd⊎ _ isFinOrdUnit _
        (isFinOrd⊎ _ (isFinOrdεTransition r) _ (isFinOrdεTransition r')))
      )
isFinOrdεTransition (r *r) =
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

