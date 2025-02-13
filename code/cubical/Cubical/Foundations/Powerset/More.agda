module Cubical.Foundations.Powerset.More where

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.MoreMore
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset renaming (ℙ to ℙ' ; _∈_ to _∈'_)

open import Cubical.Functions.Logic hiding (⊥ ; ⊤)

private
  variable
    ℓ ℓ' : Level

module Powerset (A : Type ℓ) where
  ℙ : Type (ℓ-suc ℓ)
  ℙ = ℙ' A

  ⊥ℙ : ℙ
  ⊥ℙ a = ⊥* , isProp⊥*

  ⊤ℙ : ℙ
  ⊤ℙ a = Unit* , isPropUnit*

  _∪ℙ_ : ℙ → ℙ → ℙ
  (X ∪ℙ Y) a = X a ⊔ Y a
  infixr 30 _∪ℙ_

  _∩ℙ_ : ℙ → ℙ → ℙ
  (X ∩ℙ Y) a = X a ⊓ Y a
  infixr 31 _∩ℙ_

  ¬ℙ : ℙ → ℙ
  ¬ℙ X x .fst = X x .fst → ⊥
  ¬ℙ X x .snd = isProp→ isProp⊥

  _∈_ : A → ℙ → Type ℓ
  x ∈ X = ⟨ X x ⟩

  _∉_ : A → ℙ → Type ℓ
  x ∉ X = ⟨ X x ⟩ → ⊥

  module PowersetOverSet (isSetA : isSet A) where
    ⟦_⟧ℙ : (a : A) → ℙ
    ⟦ a ⟧ℙ a' .fst = a ≡ a'
    ⟦ a ⟧ℙ a' .snd = isSetA a a'

module UniversePolymorphicPowerset ℓ' (A : Type ℓ) where
  ℙ : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  ℙ = A → hProp (ℓ-max ℓ ℓ')

  ⊥ℙ : ℙ
  ⊥ℙ a = ⊥* , isProp⊥*

  ⊤ℙ : ℙ
  ⊤ℙ a = Unit* , isPropUnit*

  _∪ℙ_ : ℙ → ℙ → ℙ
  (X ∪ℙ Y) a = X a ⊔ Y a
  infixr 30 _∪ℙ_

  _∩ℙ_ : ℙ → ℙ → ℙ
  (X ∩ℙ Y) a = X a ⊓ Y a
  infixr 31 _∩ℙ_

  ¬ℙ : ℙ → ℙ
  ¬ℙ X x .fst = X x .fst → ⊥
  ¬ℙ X x .snd = isProp→ isProp⊥

  _∈_ : A → ℙ → Type (ℓ-max ℓ ℓ')
  x ∈ X = ⟨ X x ⟩

  _∉_ : A → ℙ → Type (ℓ-max ℓ ℓ')
  x ∉ X = ⟨ X x ⟩ → ⊥

  ℙ≡ :
    (X Y : ℙ) →
    (∀ (a : A) → a ∈ X → a ∈ Y) →
    (∀ (a : A) → a ∈ Y → a ∈ X) →
    X ≡ Y
  ℙ≡ X Y X→Y Y→X = funExt (λ a → Σ≡Prop (λ _ → isPropIsProp) (hPropExt (X a .snd) (Y a .snd) (X→Y a) (Y→X a)))

  module PowersetOverSet (isSetA : isSet A) where
    ⟦_⟧ℙ : (a : A) → ℙ
    ⟦ a ⟧ℙ a' .fst = Lift {ℓ}{ℓ'} (a ≡ a')
    ⟦ a ⟧ℙ a' .snd = isPropLift (isSetA a a')
