module Cubical.Relation.Nullary.DecidablePropositions.Powerset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open Iso

private
  variable
    ℓ ℓ' : Level

module DecidablePowerset (A : Type ℓ) where
  Decℙ : Type (ℓ-suc ℓ)
  Decℙ = A → DecProp ℓ

  Decℙ' : Type (ℓ-suc ℓ)
  Decℙ' = A → DecProp' ℓ

  DecℙIso : Iso Decℙ Decℙ'
  DecℙIso .fun x a = DecPropIso .fun (x a)
  DecℙIso .inv x' a = DecPropIso .inv (x' a)
  DecℙIso .sec b = funExt (λ x → DecPropIso .sec _)
  DecℙIso .ret b = funExt (λ x → DecPropIso .ret _)

  ∅ℙ : Decℙ
  ∅ℙ x = (⊥* , isProp⊥*) , (no lower)

  inDecℙ :
    (a : A) → Decℙ → Type ℓ
  inDecℙ a X = X a .fst .fst

  Decℙ→Type : Decℙ → Type ℓ
  Decℙ→Type X = Σ[ a ∈ A ] X a .fst .fst

  _∪ℙ_ : Decℙ → Decℙ → Decℙ
  (X ∪ℙ Y) x =
    decRec
      (λ x∈X → X x .fst , yes x∈X)
      (λ x∉X →
        decRec
          (λ x∈Y → Y x .fst , yes x∈Y)
          (λ x∉Y → Y x .fst , (no x∉Y))
          (Y x .snd)
        )
      (X x .snd)
  infixr 20 _∪ℙ_

  _∩ℙ_ : Decℙ → Decℙ → Decℙ
  (X ∩ℙ Y) x = DecProp× (X x) (Y x)
  infixr 30 _∩ℙ_

  ¬ℙ : Decℙ → Decℙ
  (¬ℙ X) x = negateDecProp (X x)

  _∈ℙ_ : A → Decℙ → Type ℓ
  x ∈ℙ X = inDecℙ x X

module DecidableFinitePowerset ((A , isFinSetA) : FinSet ℓ) where
  open DecidablePowerset A
  SingletonDecℙ : (a : A) → Decℙ
  SingletonDecℙ a x =
    ((x ≡ a) ,
    isFinSet→isSet isFinSetA _ _) ,
    isFinSet→Discrete isFinSetA _ _

  ⟦_⟧ℙ : (a : A) → Decℙ
  ⟦_⟧ℙ = SingletonDecℙ

  SingletonDecℙ' : (a : A) → Decℙ'
  SingletonDecℙ' a = DecℙIso .fun (SingletonDecℙ a)

  isFinSetDecℙ : isFinSet Decℙ
  isFinSetDecℙ = isFinSet→ (A , isFinSetA) (DecProp ℓ , isFinSetDecProp)

  DiscreteDecℙ : Discrete Decℙ
  DiscreteDecℙ = isFinSet→Discrete isFinSetDecℙ

  isFinSetDecℙ' : isFinSet Decℙ'
  isFinSetDecℙ' =
    PT.rec
      isPropIsFinSet
      (λ the-eq →
        (isFinSetDecℙ .fst) ,
        ∣ compEquiv (isoToEquiv (invIso DecℙIso)) the-eq ∣₁)
      (isFinSetDecℙ .snd)

  FinSetDecℙ : FinSet (ℓ-suc ℓ)
  FinSetDecℙ = Decℙ , isFinSetDecℙ

  FinSetDecℙ' : FinSet (ℓ-suc ℓ)
  FinSetDecℙ' = Decℙ' , isFinSetDecℙ'

  _∈-FinSetDecℙ_ : A → ⟨ FinSetDecℙ ⟩ → Type ℓ
  a ∈-FinSetDecℙ X = X a .fst .fst

  Decℙ'→FinSet : Decℙ' → FinSet ℓ
  fst (Decℙ'→FinSet X) = Σ[ a ∈ A  ] ⟨ X a ⟩
  snd (Decℙ'→FinSet X) = isFinSetSub (A , isFinSetA) X

  Decℙ→FinSet : Decℙ → FinSet ℓ
  Decℙ→FinSet X = Decℙ'→FinSet (DecℙIso .fun X)


open DecidablePowerset

LiftDecℙ' : ∀ {L}{L'} (A : Type L) →
  (Decℙ' {L} A) → (Decℙ' {ℓ-max L L'} (Lift L' A))
LiftDecℙ' {L}{L'} A x a = LiftDecProp' {L}{L'} (x (lower a))

open DecidableFinitePowerset
-- I'm pretty sure this is the `bind` of a FinSet monad
FinSetDecℙ∃ :
  ∀ {ℓ} (A B : FinSet ℓ) →
  ⟨ FinSetDecℙ A ⟩ →
  (⟨ A ⟩ → ⟨ FinSetDecℙ B ⟩) → ⟨ FinSetDecℙ B ⟩
FinSetDecℙ∃ A B ℙA f b = DecProp∃ A (λ a → DecProp× (ℙA a) (f a b))

open import Cubical.Foundations.Powerset
module _ {A : Type ℓ} (X : ℙ A)
  (decidable : ∀ (a : A) → Dec (X a .fst))
  where
  toDecℙ : Decℙ A
  toDecℙ a = X a , decidable a
