open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.SubAlphabet where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.List
import Cubical.Data.Maybe as Maybe
import Cubical.Data.Equality as Eq

open import Lexer.Base

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

  SubAlphabet→Alphabet : Lexer SubAlphabet Alphabet
  SubAlphabet→Alphabet [] = Maybe.just []
  SubAlphabet→Alphabet (c ∷ w) =
    Maybe.map-Maybe
      (c .fst ∷_)
      (SubAlphabet→Alphabet w)

  Alphabet→SubAlphabet : Lexer Alphabet SubAlphabet
  Alphabet→SubAlphabet [] = Maybe.just []
  Alphabet→SubAlphabet (c ∷ w) =
    decRec
      (λ is-true → Maybe.map-Maybe ((c , is-true) ∷_) (Alphabet→SubAlphabet w))
      (λ _ → Maybe.nothing)
      (charFun c ≟ true)

  Alphabet→SubAlphabet' :
    List ⟨ Alphabet ⟩ → List ⟨ SubAlphabet ⟩
  Alphabet→SubAlphabet' [] = []
  Alphabet→SubAlphabet' (c ∷ w) =
    decRec
      (λ is-true → (c , is-true) ∷ Alphabet→SubAlphabet' w)
      (λ _ → Alphabet→SubAlphabet' w)
      (charFun c ≟ true)
