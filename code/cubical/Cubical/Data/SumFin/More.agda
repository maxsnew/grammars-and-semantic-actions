module Cubical.Data.SumFin.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More

open import Cubical.Data.SumFin hiding (elim)
open import Cubical.Data.Nat as Nat hiding (elim)

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    m n : ℕ

DecΣ : (n : ℕ) → (P : Fin n → Type ℓ) → ((k : Fin n) → Dec (P k)) → Dec (Σ (Fin n) P)
DecΣ = Nat.elim
  (λ _ _ → no fst)
  (λ n ih P decP → decP fzero & decRec
    (yes ∘ (_ ,_))
    (λ ¬Pzero → ih (P ∘ fsuc) (decP ∘ fsuc) & mapDec
      (λ (k , Pk) → (fsuc k , Pk))
      (λ ¬Psuc →
        λ { (fzero , Pzero) → ¬Pzero Pzero
          ; (fsuc k , Pk) → ¬Psuc (k , Pk)
          })))
