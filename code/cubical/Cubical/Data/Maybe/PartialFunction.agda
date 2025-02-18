module Cubical.Data.Maybe.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels.MoreMore

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Maybe.More
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.More
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓA ℓB ℓC : Level
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

  ∈domainOrNothing : (a : A) → ⟨ domain a ⟩ ⊎ (f a ≡ nothing)
  ∈domainOrNothing a with f a
  ... | nothing = inr refl
  ... | just x = inl (x , refl)

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
    disjointDomains = ∀ (a : A) → (f a ≡ nothing) ⊎ (g a ≡ nothing)

  module _ (disj-doms : disjointDomains) where
    union : A ⇀ B
    union a with (f a)
    union a | nothing with (g a)
    union a | nothing | nothing = nothing
    union a | nothing | (just b) = just b
    union a | (just b) = just b

module _
  {A : Type ℓA}
  {B : Type ℓB}
  {C : Type ℓC}
  (f : A ⇀ B)
  (g : A ⇀ C)
  where

  disjointDomains : Type (ℓ-max (ℓ-max ℓA ℓB) ℓC)
  disjointDomains = ∀ (a : A) → (f a ≡ nothing) ⊎ (g a ≡ nothing)

  module _ (disj-doms : disjointDomains) where
    union⊎ : A ⇀ (B ⊎ C)
    union⊎ a with (f a)
    ... | nothing with (g a)
    union⊎ a | nothing | nothing = nothing
    union⊎ a | nothing | just c = just (inr c)
    union⊎ a | just b = just (inl b)

    module _ (a : A) where
      open Iso

      mkFiber-f : fiber (just ∘ inl) (union⊎ a) → fiber just (f a)
      mkFiber-f (b , b≡) with f a
      mkFiber-f (b , b≡) | nothing with g a
      mkFiber-f (b , b≡) | nothing | nothing = Empty.rec (¬just≡nothing b≡)
      mkFiber-f (b , b≡) | nothing | just c =
        Empty.rec (inl≢inr (cong (fromJust-def (inl b)) b≡))
      mkFiber-f (b , b≡) | just b' = b' , refl

      mkFiber-f' : fiber just (f a) → fiber just (union⊎ a)
      mkFiber-f' (b , b≡) with f a
      mkFiber-f' (b , b≡) | nothing with g a
      mkFiber-f' (b , b≡) | nothing | nothing = Empty.rec (¬just≡nothing b≡)
      mkFiber-f' (b , b≡) | nothing | just c = Empty.rec (¬just≡nothing b≡)
      mkFiber-f' (b , b≡) | just b' = inl b' , refl

      mkFiber-f'' : fiber (just ∘ inl) (union⊎ a) → fiber just (union⊎ a)
      mkFiber-f'' (b , b≡) = inl b , b≡

      mkFiber-g : fiber (just ∘ inr) (union⊎ a) → fiber just (g a)
      mkFiber-g (c , c≡) with f a
      mkFiber-g (c , c≡) | nothing with g a
      mkFiber-g (c , c≡) | nothing | nothing = Empty.rec (¬just≡nothing c≡)
      mkFiber-g (c , c≡) | nothing | just c' = c' , refl
      mkFiber-g (c , c≡) | just b =
        Empty.rec (inl≢inr (sym (cong (fromJust-def (inl b)) c≡)))

      union⊎-map-fiber : fiber just (union⊎ a) → fiber just (f a) ⊎ fiber just (g a)
      union⊎-map-fiber (inl b , b≡) = inl (mkFiber-f (b , b≡))
      union⊎-map-fiber (inr c , c≡) = inr (mkFiber-g (c , c≡))

