open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Inductive.AsEquality.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct.AsEquality Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Inductive.AsEquality.Indexed Alphabet
import Grammar.Inductive.AsPath.Indexed Alphabet as IndPath
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX : Level

module _ {ℓA : Level} where
  ⟦_⟧≡ : {X : Type ℓX} → (F : Functor X) → IndPath.⟦ F ⟧ {ℓA = ℓA} ≡ ⟦ F ⟧
  ⟦ k A ⟧≡  = refl
  ⟦ Var x ⟧≡ = refl
  ⟦ &e Y F ⟧≡ i A = &[ y ∈ Y ] ⟦ F y ⟧≡ i A
  ⟦ ⊕e Y F ⟧≡ i A = ⊕[ y ∈ Y ] ⟦ F y ⟧≡ i A
  ⟦ F ⊗e F' ⟧≡ i A = ⊗Path≡⊗Eq {A = ⟦ F ⟧≡ i A} {B = ⟦ F' ⟧≡ i A} i
  ⟦ F &e2 F' ⟧≡ i A = ⟦ F ⟧≡ i A & ⟦ F' ⟧≡ i A

-- module _ {ℓX : Level} {X : Type ℓX} (F : X → Functor X) where
--   μ≡ : PathP (λ i → X → String → {!!}) (IndPath.μ F) (μ F)
--   μ≡ = {!!}


--   open StrongEquivalence

--   unroll≅ : ∀ x → μ F x ≅ ⟦ F x ⟧ (μ F)
--   unroll≅ x .fun = unroll F x
--   unroll≅ x .inv = roll
--   unroll≅ x .sec = refl
--   unroll≅ x .ret =
--     equalizer-ind
--       F
--       (λ x → μ F x)
--       (λ x → roll ∘g unroll F x)
--       (λ _ → id)
--       (λ x → refl)
--       x
