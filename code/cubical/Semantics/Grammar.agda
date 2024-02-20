{-# OPTIONS --lossy-unification #-}
module Semantics.Grammar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty.Base
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.Instances.FreeComMonoid

open import Cubical.Tactics.Reflection

private
  variable ℓ ℓ' : Level

module GrammarDefs ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w =
    isSetΣ (isSet× isSetString isSetString)
      λ s → isGroupoidString w (s .fst ++ s .snd)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → hSet ℓ

  open ListPath
  ILin : Grammar
  ILin w = (w ≡ []) , isGroupoidString w []

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w =
    (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × g' (s .fst .snd) .fst) ,
    isSetΣ (isSetSplitting w) λ s →
      isSet× (g (s .fst .fst) .snd) (g' (s .fst .snd) .snd)

  literal : (Σ₀ .fst) → Grammar
  literal c w = ([ c ] ≡ w) , isGroupoidString ([ c ]) w

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w =
    (∀ (w' : String) → g w' .fst × g' (w' ++ w) .fst) ,
      isSetΠ (λ w' → isSet× (g w' .snd) (g' (w' ++ w) .snd))

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w =
    (∀ (w' : String) → g (w ++ w') .fst × g' w' .fst) ,
      isSetΠ (λ w' → isSet× (g (w ++ w') .snd) (g' w' .snd))

  ΠLin : {A : hSet ℓ} → (A .fst → Grammar) → Grammar
  ΠLin {A} f w = (∀ (a : A .fst) → f a w .fst) , isSetΠ λ a → f a w .snd

  ΣLin : {A : hSet ℓ} → (A .fst → Grammar) → Grammar
  ΣLin {A} f w =
    (Σ[ a ∈ A .fst ] f a w .fst) ,
      isSetΣ (A .snd) λ a → f a w .snd

  ⊤Lin : Grammar
  ⊤Lin w = Unit* , isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = (g w .fst × g' w .fst) ,
    isSet× (g w .snd) (g' w .snd)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = (g w .fst ⊎ g' w .fst) ,
    isSet⊎ (g w .snd) (g' w .snd)

  ⊥Lin : Grammar
  ⊥Lin w = Lift ⊥ ,
    λ x y a b i →
      liftExt (isProp→isSet isProp⊥ (lower x) (lower y)
        (cong lower a) (cong lower b) i)

  _⇒_ : Grammar → Grammar → Grammar
  (g ⇒ g') w =
    (g w .fst → g' w .fst) ,
    isSetΠ (λ p → g' w .snd)

  ParseTransformer : Grammar → Grammar → Type ℓ
  ParseTransformer g g' = ∀ {w} → g w .fst → g' w .fst

  data KL*Ty (g : Grammar) : (w : String) → Type ℓ where
    nil : (KL*Ty g [])
    cons :
      ∀ {w w'} →
        g w .fst × KL*Ty g w' → KL*Ty g (w ++ w')
      -- (Σ[ s ∈ Splitting w ]
        -- g (s .fst .fst) .fst × KL*Ty g (s .fst .snd)) → KL*Ty g w

  module isSetKL*TyProof (g : Grammar) where
    KL*Ty-X = String

    KL*Ty-S : KL*Ty-X → Type {!!}
    KL*Ty-S w =
      (w ≡ []) ⊎
      (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst)

    KL*Ty-P : ∀ w → KL*Ty-S w → Type {!!}
    KL*Ty-P w (inl x) = Lift ⊥
    KL*Ty-P w (inr (s , p)) = KL*Ty g (s .fst .snd)

    KL*Ty-inX : ∀ w (s : KL*Ty-S w) → KL*Ty-P w s → KL*Ty-X
    KL*Ty-inX w (fsuc (s , parse)) p = s .fst .snd

    KL*Ty→W : ∀ {w} → KL*Ty g w → IW KL*Ty-S KL*Ty-P KL*Ty-inX w
    KL*Ty→W {.[]} nil = node (inl refl) λ ()
    KL*Ty→W {.(_ ++ _)} (cons {w}{w'} x) =
      node (fsuc (((w , w') , refl) , (x .fst)))
        (λ p → KL*Ty→W (x .snd))

    W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
    W→KL*Ty (node (inl x) subtree) =
      transport (cong (λ a → KL*Ty g a) (sym x)) (KL*Ty.nil {g = g})
    W→KL*Ty (node (fsuc x) subtree) =
      transport {!!}
        (KL*Ty.cons {g = g} ((x .snd) ,
        (W→KL*Ty (subtree {!!}))))

  -- isSetKL*Ty : (g : Grammar) → (w : String) → isSet (KL*Ty g w)
  -- isSetKL*Ty g w = {!!}

  -- KL* : (g : Grammar) → Grammar
  -- KL* g w = (KL*Ty g w , isSetKL*Ty g w)
