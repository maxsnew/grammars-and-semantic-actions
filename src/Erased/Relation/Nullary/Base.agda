module Erased.Relation.Nullary.Base where

open import Erased.Data.Empty.Base
import Erased.Data.Equality.Base as Eq
open import Erased.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

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

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥₁) public

@0 SplitSupport : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥₁ → A

@0 Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ∈ (A → A) ] 2-Constant f

@0 Populated ⟪_⟫ : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)
⟪_⟫ = Populated

@0 PStable : Type ℓ → Type ℓ
PStable A = ⟪ A ⟫ → A

onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllPaths S A = (x y : A) → S (x ≡ y)

onAllEqs : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllEqs S A = (x y : A) → S (x Eq.≡ y)

Separated : Type ℓ → Type ℓ
Separated = onAllPaths Stable

@0 HSeparated : Type ℓ → Type ℓ
HSeparated = onAllPaths SplitSupport

@0 Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ = onAllPaths Collapsible

@0 PStable≡ : Type ℓ → Type ℓ
PStable≡ = onAllPaths PStable

Discrete : Type ℓ → Type ℓ
Discrete = onAllPaths Dec

DiscreteEq : Type ℓ → Type ℓ
DiscreteEq = onAllEqs Dec
