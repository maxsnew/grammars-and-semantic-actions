{-# OPTIONS --erased-cubical #-}

module Erased.Data.FinSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop

open import Erased.Data.Nat.Base
open import Erased.Data.Nat.Properties
open import Erased.Data.Unit
open import Erased.Data.Bool.Base
open import Erased.Data.Empty as Empty
open import Erased.Data.Sigma.Base

-- open import Erased.Data.Fin.Base renaming (Fin to Finℕ)
open import Erased.Data.SumFin.Base
open import Erased.Data.SumFin.Properties
open import Erased.Data.FinSet.Base
import Erased.Data.Equality as Eq

open import Erased.Relation.Nullary.Base
-- open import Cubical.Relation.Nullary.HLevels

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- operators to more conveniently compose equivalences

module _
  {A : Type ℓ}{B : Type ℓ'}{C : Type ℓ''} where

  infixr 30 _⋆̂_

  @0 _⋆̂_ : ∥ A ≃ B ∥₁ → ∥ B ≃ C ∥₁ → ∥ A ≃ C ∥₁
  _⋆̂_ = Prop.map2 (_⋆_)

module _
  {A : Type ℓ}{B : Type ℓ'} where

  @0 ∣invEquiv∣ : ∥ A ≃ B ∥₁ → ∥ B ≃ A ∥₁
  ∣invEquiv∣ = Prop.map invEquiv

-- useful implications

@0 EquivPresIsFinSet : A ≃ B → isFinSet A → isFinSet B
EquivPresIsFinSet e (_ , p) = _ , ∣ invEquiv e ∣₁ ⋆̂ p

@0 isFinSetFin : {n : ℕ} → isFinSet (Fin n)
isFinSetFin = _ , ∣ idEquiv _ ∣₁

-- isFinSetUnit : isFinSet Unit
-- isFinSetUnit = 1 , ∣ invEquiv Fin1≃Unit ∣₁

-- isFinSetBool : isFinSet Bool
-- isFinSetBool = 2 , ∣ invEquiv SumFin2≃Bool ∣₁

-- isFinSet→Discrete : isFinSet A → Discrete A
-- isFinSet→Discrete h = Prop.rec isPropDiscrete (λ p → EquivPresDiscrete (invEquiv p) discreteFin) (h .snd)

open IsoEq
isFinOrd'→DecEq : isFinOrd' A → DecEq A
isFinOrd'→DecEq isFinOrdA a a' with decEqFin (isFinOrdA .fst) (isFinOrdA .snd .fun a) (isFinOrdA .snd .fun a')
... | yes p = yes (Eq.sym (isFinOrdA .snd .leftInv a) Eq.∙ Eq.ap (isFinOrdA .snd .inv) p Eq.∙ isFinOrdA .snd .leftInv a')
... | no p = no (λ x → p (Eq.ap (isFinOrdA .snd .fun) x))

-- isContr→isFinSet : isContr A → isFinSet A
-- isContr→isFinSet h = 1 , ∣ isContr→≃Unit h ⋆ invEquiv Fin1≃Unit ∣₁

-- isDecProp→isFinSet : isProp A → Dec A → isFinSet A
-- isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
-- isDecProp→isFinSet h (no ¬p) = 0 , ∣ uninhabEquiv ¬p (idfun _) ∣₁

-- isDec→isFinSet∥∥ : Dec A → isFinSet ∥ A ∥₁
-- isDec→isFinSet∥∥ dec = isDecProp→isFinSet isPropPropTrunc (Dec∥∥ dec)

-- isFinSet→Dec∥∥ : isFinSet A → Dec ∥ A ∥₁
-- isFinSet→Dec∥∥ h =
--   Prop.rec (isPropDec isPropPropTrunc)
--       (λ p → EquivPresDec (propTrunc≃ (invEquiv p)) (Dec∥Fin∥ _)) (h .snd)

-- isFinProp→Dec : isFinSet A → isProp A → Dec A
-- isFinProp→Dec p h = subst Dec (propTruncIdempotent h) (isFinSet→Dec∥∥ p)

-- PeirceLaw∥∥ : isFinSet A → NonEmpty ∥ A ∥₁ → ∥ A ∥₁
-- PeirceLaw∥∥ p = Dec→Stable (isFinSet→Dec∥∥ p)

-- PeirceLaw : isFinSet A → NonEmpty A → ∥ A ∥₁
-- PeirceLaw p q = PeirceLaw∥∥ p (λ f → q (λ x → f ∣ x ∣₁))

-- -- transprot family towards Fin

-- transpFamily :
--     {A : Type ℓ}{B : A → Type ℓ'}
--   → ((n , e) : isFinOrd A) → (x : A) → B x ≃ B (invEq e (e .fst x))
-- transpFamily {B = B} (n , e) x = pathToEquiv (λ i → B (retEq e x (~ i)))
