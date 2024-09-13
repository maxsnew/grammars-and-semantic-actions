open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.List
open import Cubical.Data.FinSet

open import Cubical.Data.Sigma

open import Helper

String : Type ℓ-zero
String = List ⟨ Alphabet ⟩

Splitting : String → Type ℓ-zero
Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

isSetString : isSet String
isSetString = isOfHLevelList 0 (str Alphabet)

isGroupoidString : isGroupoid String
isGroupoidString = isSet→isGroupoid isSetString

isSetSplitting : (w : String) → isSet (Splitting w)
isSetSplitting w =
  isSetΣ (isSet× isSetString isSetString)
    λ s → isGroupoidString w (s .fst ++ s .snd)

SplittingPathP :
  ∀ {w : I → String}{s0 : Splitting (w i0)}{s1 : Splitting (w i1)}
  → s0 .fst ≡ s1 .fst
  → PathP (λ i → Splitting (w i)) s0 s1
SplittingPathP s≡ = ΣPathPProp (λ _ → isSetString _ _) s≡

Splitting≡ : ∀ {w} → {s s' : Splitting w}
  → s .fst ≡ s' .fst
  → s ≡ s'
Splitting≡ = SplittingPathP

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  DiscreteAlphabet : Discrete ⟨ Alphabet ⟩
  DiscreteAlphabet = isFinSet→Discrete isFinSetAlphabet

  DiscreteString : Discrete String
  DiscreteString = discreteList DiscreteAlphabet

module _ (c : ⟨ Alphabet ⟩) where
  splitChar : (w : String) → Splitting (c ∷ w)
  splitChar w = ([ c ] , w) , refl
