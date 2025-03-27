open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module String.SubAlphabet where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe

open import String.Base

-- Pick out a subalphabet of another alphabet
module _
  (Alphabet : hSet ℓ-zero)
  (charFun : ⟨ Alphabet ⟩ → Bool)
  where

  SubAlphabet' : Type ℓ-zero
  SubAlphabet' = Σ[ c ∈ ⟨ Alphabet ⟩ ] charFun c ≡ true

  opaque
    isSetSubAlphabet : isSet SubAlphabet'
    isSetSubAlphabet =
      isSetΣ
        (Alphabet .snd)
        λ _ → isSet→isGroupoid isSetBool _ _

  SubAlphabet : hSet ℓ-zero
  SubAlphabet .fst = SubAlphabet'
  SubAlphabet .snd = isSetSubAlphabet

  SubAlphabet→Alphabet : String SubAlphabet → Maybe (String Alphabet)
  SubAlphabet→Alphabet [] = Maybe.just []
  SubAlphabet→Alphabet (c ∷ w) =
    map-Maybe
      (c .fst ∷_)
      (SubAlphabet→Alphabet w)

  Alphabet→SubAlphabet : String Alphabet → Maybe (String SubAlphabet)
  Alphabet→SubAlphabet [] = Maybe.just []
  Alphabet→SubAlphabet (c ∷ w) =
    decRec
      (λ is-true → map-Maybe ((c , is-true) ∷_) (Alphabet→SubAlphabet w))
      (λ _ → Maybe.nothing)
      (charFun c ≟ true)

  Alphabet→SubAlphabet' : String Alphabet → String SubAlphabet
  Alphabet→SubAlphabet' [] = []
  Alphabet→SubAlphabet' (c ∷ w) =
    decRec
      (λ is-true → (c , is-true) ∷ Alphabet→SubAlphabet' w)
      (λ _ → Alphabet→SubAlphabet' w)
      (charFun c ≟ true)
