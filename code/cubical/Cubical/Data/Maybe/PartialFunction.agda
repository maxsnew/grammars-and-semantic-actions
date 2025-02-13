module Cubical.Data.Maybe.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.MoreMore

open import Cubical.Functions.Embedding

open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

private
  variable
    ℓ ℓA ℓB ℓC : Level
    A : Type ℓA
    B : Type ℓB
    C : Type ℓC

partialFunction : Type ℓA → Type ℓB → Type (ℓ-max ℓA ℓB)
partialFunction A B = A → Maybe B

_⇀_ : Type ℓA → Type ℓB → Type (ℓ-max ℓA ℓB)
_⇀_ = partialFunction

compose :
  A ⇀ B →
  B ⇀ C →
  A ⇀ C
compose f g a = Maybe.rec nothing g (f a)

module _
  {A : Type ℓA}
  {B : Type ℓB}
  (f : A ⇀ B)
  where

  domain : A → hProp ℓB
  domain a .fst = fiber just (f a)
  domain a .snd = isEmbedding→hasPropFibers isEmbedding-just (f a)

  isTotal : Type _
  isTotal = ∀ (a : A) → ⟨ domain a ⟩

  mkFun : isTotal → A → B
  mkFun total a = total a .fst

total→partial : (A → B) → A ⇀ B
total→partial f a = just (f a)

module _
  {A : Type ℓA}
  {B : Type ℓB}
  (f g : A ⇀ B)
  where

  private
    disjointDomains : Type (ℓ-max ℓA ℓB)
    disjointDomains = ∀ (a : A) → (⟨ domain f a ⟩ → ⊥) ⊎ (⟨ domain g a ⟩ → ⊥)

  module _ (disj-doms : disjointDomains) where
    union : A ⇀ B
    union a =
      Sum.rec
        (λ a∉domf → g a)
        (λ a∉domg → f a)
        (disj-doms a)

module _
  {A : Type ℓA}
  {B : Type ℓB}
  {C : Type ℓC}
  (f : A ⇀ B)
  (g : A ⇀ C)
  where

  disjointDomains : Type (ℓ-max (ℓ-max ℓA ℓB) ℓC)
  disjointDomains = ∀ (a : A) → (⟨ domain f a ⟩ → ⊥) ⊎ (⟨ domain g a ⟩ → ⊥)

  module _ (disj-doms : disjointDomains) where
    union⊎ : A ⇀ (B ⊎ C)
    union⊎ a =
      Sum.rec
        (λ a∉domf → map-Maybe inr (g a))
        (λ a∉domg → map-Maybe inl (f a))
        (disj-doms a)
