{-# OPTIONS --erased-cubical #-}
module Erased.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Data.FinSet

open import Erased.Data.Empty.Base as ⊥
import Erased.Data.Equality.Base as Eq
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ  : Level
    A  : Type ℓ

-- Negation
infix 3 ¬_

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- Decidable types (inspired by standard library)
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

decRec : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → (P → A) → (¬ P → A) → (Dec P) → A
decRec ifyes ifno (yes p) = ifyes p
decRec ifyes ifno (no ¬p) = ifno ¬p

decElim : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Dec P → Type ℓ'} →
  ((p : P) → A (yes p)) → ((¬p : ¬ P) → A (no ¬p)) →
  (x : Dec P) → A x
decElim ifyes ifno (yes p) = ifyes p
decElim ifyes ifno (no ¬p) = ifno ¬p

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥₁) public

onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllPaths S A = (x y : A) → S (x ≡ y)

onAllEqs : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllEqs S A = (x y : A) → S (x Eq.≡ y)

Discrete : Type ℓ → Type ℓ
Discrete = onAllPaths Dec

DecEq : Type ℓ → Type ℓ
DecEq = onAllEqs Dec

-- module _ {A : Type ℓ} (isFinSetA : isFinSet A) where
--   isFinSet→DecEq : DecEq A
--   isFinSet→DecEq = {!!}
