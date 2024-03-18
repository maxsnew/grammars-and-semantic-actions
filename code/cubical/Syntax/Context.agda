module Syntax.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

private
  variable ℓ ℓ' : Level

Sig₀ : (ℓ : Level) → Type (ℓ-suc ℓ)
Sig₀ ℓ = hGroupoid ℓ

module _ (Σ₀ : Sig₀ ℓ-zero) where
  data IntCtx : Type {!!}
  Tys : IntCtx → Type {!!}
  Vars : IntCtx → Type {!!}
  El :  wq

  data IntCtx where
    nil : IntCtx
    _∷_ : (Γ : IntCtx) → {!!} → IntCtx

  Tys nil = ⊤
  Tys (Γ ∷ B) = Tys Γ × {!!}

  Vars nil = ⊥
  Vars (Γ ∷ B) = Vars Γ ⊎ ⊤
