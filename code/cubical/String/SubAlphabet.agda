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
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate

open import Cubical.HITs.PropositionalTruncation as PT

open import Helper

-- Pick out a subalphabet of another alphabet
module _
  (Alphabet Alphabet' : hSet ℓ-zero)
  (embed : ⟨ Alphabet ⟩ ↪ ⟨ Alphabet' ⟩)
  where
  SubAlphabet' : Type ℓ-zero
  SubAlphabet' = Σ[ c ∈ ⟨ Alphabet' ⟩ ] fiber (embed .fst) c

  SubAlphabetIso :
    Iso ⟨ Alphabet ⟩ (Σ ⟨ Alphabet' ⟩ (λ v → fiber (λ z → embed .fst z) v))
  SubAlphabetIso =
     iso
       (λ x → (embed .fst x) , (x , refl))
       (λ x → x .snd .fst)
       (λ b →
         Σ≡Prop (λ x → isEmbedding→hasPropFibers (embed .snd) x)
           (b .snd .snd))
       (λ _ → refl)

  open Iso
  isSetSubAlphabet : isSet SubAlphabet'
  isSetSubAlphabet =
    isSetRetract (SubAlphabetIso .inv) (SubAlphabetIso .fun)
      (SubAlphabetIso .rightInv) (Alphabet .snd)

  SubAlphabet : hSet ℓ-zero
  SubAlphabet .fst = SubAlphabet'
  SubAlphabet .snd = isSetSubAlphabet

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    isFinSetSubAlphabet : isFinSet SubAlphabet'
    isFinSetSubAlphabet =
      EquivPresIsFinSet (isoToEquiv SubAlphabetIso) isFinSetAlphabet

    module _ (DiscreteAlphabet' : Discrete ⟨ Alphabet' ⟩) where
      maybe-SubAlphabet : ⟨ Alphabet' ⟩ → Maybe ⟨ SubAlphabet ⟩
      maybe-SubAlphabet c' =
        decRec
          (λ ∣in-image∣ →
            just
              (c' ,
              (PT.rec (isEmbedding→hasPropFibers (embed .snd) c')
                (λ in-image → in-image) ∣in-image∣)))
          (λ ¬|in-image∣ → nothing)
          (DecProp∃
            (_ , isFinSetAlphabet)
            (λ c → (_ , Alphabet' .snd _ _) ,
                   (DiscreteAlphabet' (embed .fst c) c'))
            .snd )
