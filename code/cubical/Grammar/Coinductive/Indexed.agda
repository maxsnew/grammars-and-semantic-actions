{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  module _ {X : Type ℓX} where
    {-# NO_POSITIVITY_CHECK #-}
    record ν (F : X → Functor X) x (w : String) : Type ℓX where
      coinductive
      field unrollν : ⟦ F x ⟧ (ν F) w

    {-# ETA ν #-}

    open ν
    module _ (F : X → Functor X) x where
      unrollν' : ν F x ⊢ ⟦ F x ⟧ (ν F)
      unrollν' w z = unrollν z
  open ν public

  module _ {X : Type ℓX} (F : X → Functor X) where
    Coalgebra : (X → Grammar ℓA) → Type (ℓ-max ℓX ℓA)
    Coalgebra A = ∀ x → A x ⊢ ⟦ F x ⟧ A

    terminalCoalgebra : Coalgebra (ν F)
    terminalCoalgebra = unrollν' F

    Cohomomorphism : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB} → Coalgebra A → Coalgebra B → Type _
    Cohomomorphism {A = A}{B} α β =
      Σ[ ϕ ∈ (∀ x → A x ⊢ B x) ] (∀ (x : X) → β x ∘g ϕ x ≡ map (F x) ϕ ∘g α x)

    idCohomo : ∀ {A : X → Grammar ℓA} → (α : Coalgebra A) → Cohomomorphism α α
    idCohomo α = (λ x → id) , λ x → cong (_∘g α x) (sym (map-id (F x)))

    compCohomo : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
      (α : Coalgebra A)(β : Coalgebra B)(η : Coalgebra C)
      → Cohomomorphism β η → Cohomomorphism α β → Cohomomorphism α η
    compCohomo α β η ϕ ψ .fst x = ϕ .fst x ∘g ψ .fst x
    compCohomo α β η ϕ ψ .snd x =
      cong (_∘g ψ .fst x) (ϕ .snd x)
      ∙ cong ((map (F x) (ϕ .fst)) ∘g_) (ψ .snd x)
      ∙ cong (_∘g α x) (sym (map-∘ (F x) (ϕ .fst) (ψ .fst)))

    module _ {A : X → Grammar ℓA} (α : Coalgebra A) where
      {-# TERMINATING #-}
      corecCohomo : Cohomomorphism α terminalCoalgebra
      corecCohomo .fst x w z .unrollν = map (F x) (corecCohomo .fst) w (α x w z)
      corecCohomo .snd x = refl

      corec : ∀ x → A x ⊢ (ν F x)
      corec = corecCohomo .fst

    rollν : ∀ x → ⟦ F x ⟧ (ν F) ⊢ ν F x
    rollν x w z .unrollν = z

    rollν' : ∀ x → ⟦ F x ⟧ (ν F) ⊢ ν F x
    rollν' = corec coalg
      where
      coalg : Coalgebra λ x → ⟦ F x ⟧ (ν F)
      coalg x = map (F x) λ x' → unrollν' F x'
