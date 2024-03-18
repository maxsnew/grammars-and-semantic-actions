module IndexedCoproduct where

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool

module _ {ℓ ℓ' ℓS} (C : Category ℓ ℓ') where
  open Category C

  module _ {coprod : ob} {S : hSet ℓS} (IdxObjs : S .fst → ob) (iₛ : (s : S .fst) → Hom[ IdxObjs s , coprod ]) where
    isIndexedCoproduct : Type (ℓ-max (ℓ-max ℓ ℓ') ℓS)
    isIndexedCoproduct = ∀ {z : ob} (f : (s : S .fst) → Hom[ IdxObjs s , z ]) →
      ∃![ g ∈ Hom[ coprod , z ] ] ∀ s → (iₛ s) ⋆ g ≡ f s

    isPropIsIndexedCoproduct : isProp isIndexedCoproduct
    isPropIsIndexedCoproduct = isPropImplicitΠ (λ z → isPropΠ λ f → isPropIsContr)

  record IndexedCoproduct {S : hSet ℓS} (IdxObjs : S .fst → ob) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓS) where
    field
      coprodOb : ob
      iₛ : (s : S .fst) → Hom[ IdxObjs s , coprodOb ]
      univprop : isIndexedCoproduct {coprodOb} {S} IdxObjs iₛ

  IndexedCoproducts : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
  IndexedCoproducts = ∀ {S} IdxObjs → IndexedCoproduct {S} IdxObjs

  -- A binary coproduct is an indexed coproduct over Bool

  ob-idx-by-bool : (a b : ob) → Bool → ob
  ob-idx-by-bool a b true = a
  ob-idx-by-bool a b false = b

  fun-idx-by-bool : {a b c : ob} (f : Hom[ a , c ]) → (g : Hom[ b , c ]) →
    (s : Lift {ℓ-zero}{ℓS} Bool) → Hom[ ob-idx-by-bool a b (lower s) , c ]
  fun-idx-by-bool f g (lift true) = f
  fun-idx-by-bool f g (lift false) = g

  open BinCoproduct
  open IndexedCoproduct

  isSetLiftBool : isSet (Lift {ℓ-zero}{ℓS} Bool)
  isSetLiftBool x y a b i =
    liftExt
      (isSetBool (lower (x)) (lower y)
      (cong lower a) (cong lower b) i)

  IndexedToBinary : (a b : ob) →
    (IndexedCoproduct
      {Lift {ℓ-zero}{ℓS} Bool , isSetLiftBool}
     (λ x → ob-idx-by-bool a b (lower x)))
    → BinCoproduct C a b
  binCoprodOb (IndexedToBinary a b x) = x .coprodOb
  binCoprodInj₁ (IndexedToBinary a b x) = x .iₛ (lift true)
  binCoprodInj₂ (IndexedToBinary a b x) = x .iₛ (lift false)
  fst (fst (univProp (IndexedToBinary a b x) {c} f g)) =
    x .univprop (fun-idx-by-bool f g) .fst .fst
  snd (fst (univProp (IndexedToBinary a b x) f g)) =
    x .univprop (fun-idx-by-bool f g) .fst .snd (lift true) ,
    x .univprop (fun-idx-by-bool f g) .fst .snd (lift false)
  snd (univProp (IndexedToBinary a b x) f g) y =
    Σ≡Prop
      (λ x₁ → isProp×
        (isSetHom (binCoprodInj₁ (IndexedToBinary a b x) ⋆ x₁) f)
        (isSetHom (binCoprodInj₂ (IndexedToBinary a b x) ⋆ x₁) g))
      (cong fst
        (x .univprop (fun-idx-by-bool f g) .snd
          ((y .fst) , λ s → path-idx-by-bool s)
        )
      )
      where
      path-idx-by-bool : (s : Lift {ℓ-zero}{ℓS} Bool) →
        iₛ x s ⋆ y .fst ≡ fun-idx-by-bool f g s
      path-idx-by-bool (lift true) = y .snd .fst
      path-idx-by-bool (lift false) = y .snd .snd

  -- BinaryToIndexed : (a b : ob) →
  --   BinCoproduct C a b →
  --   (IndexedCoproduct
  --     {Lift {ℓ-zero}{ℓS} Bool , isSetLiftBool}
  --    (λ x → ob-idx-by-bool a b (lower x)))
  -- coprodOb (BinaryToIndexed a b bincoprod) = bincoprod .binCoprodOb
  -- iₛ (BinaryToIndexed a b bincoprod) (lift true) = bincoprod .binCoprodInj₁
  -- iₛ (BinaryToIndexed a b bincoprod) (lift false) = bincoprod .binCoprodInj₂
  -- fst (fst (univprop (BinaryToIndexed a b bincoprod) f)) =
  --   bincoprod .univProp (f (lift true)) (f (lift false)) .fst .fst
  -- snd (fst (univprop (BinaryToIndexed a b bincoprod) f)) (lift true) =
  --    bincoprod .univProp (f (lift true)) (f (lift false)) .fst .snd .fst
  -- snd (fst (univprop (BinaryToIndexed a b bincoprod) f)) (lift false) =
  --    bincoprod .univProp (f (lift true)) (f (lift false)) .fst .snd .snd
  -- snd (univprop (BinaryToIndexed a b bincoprod) f) y =
  --   Σ≡Prop
  --     (λ x → isPropΠ
  --       (λ x₁ → isSetHom
  --               (iₛ (BinaryToIndexed a b bincoprod) x₁ ⋆ x) (f x₁)))
  --     (cong fst (bincoprod .univProp
  --       (f (lift true)) (f (lift false)) .snd
  --         ((y .fst) , ((y .snd (lift true)) , (y .snd (lift false))))
  --     ))
  -- Binary-is-indexed-by-bool : (a b : ob) →
  --   Iso (BinCoproduct C a b)
  --   (IndexedCoproduct
  --     {Lift {ℓ-zero}{ℓS} Bool , isSetLiftBool}
  --    (λ x → ob-idx-by-bool a b (lower x)))
  -- Iso.fun (Binary-is-indexed-by-bool a b) = BinaryToIndexed a b
  -- Iso.inv (Binary-is-indexed-by-bool a b) = IndexedToBinary a b
  -- Iso.rightInv (Binary-is-indexed-by-bool a b) idxcoprod = {!!}
  -- Iso.leftInv (Binary-is-indexed-by-bool a b) = {!!}
