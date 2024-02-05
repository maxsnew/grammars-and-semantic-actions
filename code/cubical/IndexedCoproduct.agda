module IndexedCoproduct where

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base

module _ {ℓ ℓ' ℓS} (S : hSet ℓS) (C : Category ℓ ℓ') where
  open Category C

  module _ {coprod : ob} (IdxObjs : S .fst → ob) (iₛ : (s : S .fst) → Hom[ IdxObjs s , coprod ]) where
    isIndexedCoproduct : Type (ℓ-max (ℓ-max ℓ ℓ') ℓS)
    isIndexedCoproduct = ∀ {z : ob} (f : (s : S .fst) → Hom[ IdxObjs s , z ]) →
      ∃![ g ∈ Hom[ coprod , z ] ] ∀ {s} → (iₛ s) ⋆ g ≡ f s

    isPropIsIndexedCoproduct : isProp isIndexedCoproduct
    isPropIsIndexedCoproduct = isPropImplicitΠ (λ z → isPropΠ λ f → isPropIsContr)

  record IndexedCoproduct (IdxObjs : S .fst → ob) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓS) where
    field
      coprodOb : ob
      iₛ : (s : S .fst) → Hom[ IdxObjs s , coprodOb ]
      univprop : isIndexedCoproduct IdxObjs iₛ
