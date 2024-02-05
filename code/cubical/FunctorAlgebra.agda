module FunctorAlgebra where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Initial
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

module _ {ℓ ℓ' : Level} {C : Category ℓ ℓ'} (F : Functor C C) where
  open Category
  open Functor

  record FAlgebra : Type (ℓ-max ℓ ℓ') where
    field
      carrier : C .ob
      algebra : C [ F .F-ob carrier , carrier ]

  open FAlgebra

  FAlgebra-morphism : FAlgebra → FAlgebra → Type ℓ'
  FAlgebra-morphism α β =
    Σ[ m ∈ C [ α .carrier , β .carrier  ] ]
      F .F-hom m ⋆⟨ C ⟩ β .algebra ≡ α .algebra ⋆⟨ C ⟩ m

  F-ALGEBRA : Category (ℓ-max ℓ ℓ') ℓ'
  ob F-ALGEBRA = FAlgebra
  Hom[_,_] F-ALGEBRA = FAlgebra-morphism
  fst (id F-ALGEBRA {x}) = C .id
  snd (id F-ALGEBRA {x}) =
    cong (λ a → a ⋆⟨ C ⟩ x .algebra) (F .F-id) ∙ C .⋆IdL (x .algebra) ∙ sym (C .⋆IdR (x .algebra))
  fst (_⋆_ F-ALGEBRA {x} {y} {z} f g) = f .fst ⋆⟨ C ⟩ g .fst
  snd (_⋆_ F-ALGEBRA {x} {y} {z} f g) =
    cong (λ a → a ⋆⟨ C ⟩ z .algebra) (F .F-seq (f .fst) (g .fst)) ∙
    C .⋆Assoc _ _ _ ∙
    cong (λ a → F .F-hom (f .fst) ⋆⟨ C ⟩ a) (g .snd) ∙
    sym (C .⋆Assoc _ _ _) ∙
    cong (λ a → a ⋆⟨ C ⟩ g .fst) (f .snd) ∙
    C .⋆Assoc _ _ _ 
  ⋆IdL F-ALGEBRA {x}{y} f =
    Σ≡Prop
    (λ g → C .isSetHom (seq' C (F .F-hom g) (y .algebra)) (seq' C (x .algebra) g))
    (C .⋆IdL (f .fst))
  ⋆IdR F-ALGEBRA {x}{y} f =
    Σ≡Prop
    (λ g → C .isSetHom (seq' C (F .F-hom g) (y .algebra)) (seq' C (x .algebra) g))
    (C .⋆IdR (f .fst))
  ⋆Assoc F-ALGEBRA f g h =
    Σ≡Prop
    (λ x → C .isSetHom (seq' C (F .F-hom x) (_ .algebra)) (seq' C (_ .algebra) x))
    (C .⋆Assoc _ _ _)
  isSetHom F-ALGEBRA {x} {y} =
    isSetΣ
    (C .isSetHom)
    λ z → isProp→isSet (C .isSetHom (seq' C (F .F-hom z) (y .algebra)) (seq' C (x .algebra) z))

  initial-algebra : Type (ℓ-max ℓ ℓ')
  initial-algebra = Initial F-ALGEBRA
