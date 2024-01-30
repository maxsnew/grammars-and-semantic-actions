{-# OPTIONS --lossy-unification #-}
module Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

private
  variable ℓ ℓ' : Level

module Semantics ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w = isSetΣ (isSet× isSetString isSetString) λ s → isGroupoidString w (s .fst ++ s .snd)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → hSet ℓ

  open ListPath
  ILin : Grammar
  ILin w = (w ≡ []) , isGroupoidString w []

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w = (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × g' (s .fst .snd) .fst) ,
    isSetΣ (isSetSplitting w) λ s → isSet× (g (s .fst .fst) .snd) (g' (s .fst .snd) .snd)

  literal : (Σ₀ .fst) → Grammar
  literal c w = ([ c ] ≡ w) , isGroupoidString ([ c ]) w

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w = (Σ[ w' ∈ String ] g w .fst × g' (w' ++ w) .fst) ,
    isSetΣ isSetString λ w' → isSet× (g w .snd) (g' (w' ++ w) .snd)

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w = (Σ[ w' ∈ String ] g (w ++ w') .fst × g' w .fst) ,
    isSetΣ isSetString λ w' → isSet× (g (w ++ w') .snd) (g' w .snd)

  -- ΠLin : Grammar
  -- ΠLin :

  -- ΣLin : Grammar
  -- ΣLin :

  ⊤Lin : Grammar
  ⊤Lin w = Unit* , isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = (g w .fst × g' w .fst) ,
    isSet× (g w .snd) (g' w .snd)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = (g w .fst ⊎ g' w .fst) ,
    isSet⊎ (g w .snd) (g' w .snd)

  -- KL*gg : Grammar → Grammar
  -- KL*gg g = ILin ⊕ (g ⊗ (KL*gg g))

  data KL*Ty (g : Grammar) (w : String) : Type ℓ where
    nil : ILin w .fst → (KL*Ty g w)
    cons : (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × KL*Ty g (s .fst .snd)) → KL*Ty g w

  isSetKL*Ty : (g : Grammar) → (w : String) → isSet (KL*Ty g w)
  isSetKL*Ty g w = {!!}

  KL* : (g : Grammar) → Grammar
  KL* g w = (KL*Ty g w , isSetKL*Ty g w)


  data NFA₀ (c : Σ₀ .fst) (w : String) (state : Fin 2) : Type (ℓ-suc ℓ)
  data NFA⊗ (g g' : Grammar) (w : String) : Type (ℓ-suc ℓ)
  data NFA (g : Grammar) (w : String) : Type (ℓ-suc ℓ)
  data NFA₀ c w s where
    start : (literal c) w .fst → NFA₀ c ([]) (fsuc fzero) → NFA₀ c w s
    end : s ≡ fsuc fzero → NFA₀ c w s
  data NFA⊗ g g' w where
  data NFA g w where
    times : Σ[ (g₁ , g₂) ∈ Grammar × Grammar ] ((g ≡ g₁ ⊗ g₂) × NFA⊗ g₁ g₂ w) → NFA g w
    lit : Σ[ c ∈ Σ₀ .fst ] ((g ≡ literal c) × NFA₀ c w fzero) → NFA g w

module _ where
  data αβ : Set ℓ-zero where
    α : αβ
    β : αβ

  isSetαβ : isSet αβ
  isSetαβ = {!!}

  open Semantics ℓ-zero (αβ , isSetαβ)
  w : String
  w = α ∷ β ∷ α ∷ β ∷ α ∷ []

  g : Grammar
  g = (KL* (literal α ⊗ literal β) ⊗ literal α)

  p : g w .fst
  p = ((α ∷ β ∷ α ∷ β ∷ [] , α ∷ []) , refl) ,
      cons (((α ∷ β ∷ [] , α ∷ β ∷ []) , refl) ,
           ((([ α ] , [ β ]) , refl) , (refl , refl)) ,
           (cons ((((α ∷ β ∷ []) , []) , refl) ,
             (((([ α ] , [ β ]) , refl) , (refl , refl)) , (nil refl))))) ,
      refl

  w' = α ∷ []

  pnfa : NFA₀ α w' (fsuc fzero)
  pnfa = start refl (end refl)
