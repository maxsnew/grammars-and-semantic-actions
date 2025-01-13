{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet public

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ where
  module _ {A : Type ℓ} where
    {-# NO_POSITIVITY_CHECK #-}
    record ν (F : A → Functor A) a (w : String) : Type ℓ where
      coinductive
      field unrollν : ⟦ F a ⟧ (ν F) w

    {-# ETA ν #-}

    open ν
    module _ (F : A → Functor A) a where
      unrollν' : ν F a ⊢ ⟦ F a ⟧ (ν F)
      unrollν' w x = unrollν x
  open ν public

  module _ {A : Type ℓ} (F : A → Functor A) where
    Coalgebra : (A → Grammar ℓ') → Type (ℓ-max ℓ ℓ')
    Coalgebra g = ∀ a → g a ⊢ ⟦ F a ⟧ g

    terminalCoalgebra : Coalgebra (ν F)
    terminalCoalgebra = unrollν' F

    Cohomomorphism : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''} → Coalgebra g → Coalgebra h → Type _
    Cohomomorphism {g = g}{h} α β =
      Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ] (∀ (a : A) → β a ∘g ϕ a ≡ map (F a) ϕ ∘g α a)

    idCohomo : ∀ {g : A → Grammar ℓ'} → (α : Coalgebra g) → Cohomomorphism α α
    idCohomo α = (λ a → id) , λ a → cong (_∘g α a) (sym (map-id (F a)))

    compCohomo : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}{k : A → Grammar ℓ'''}
      (α : Coalgebra g)(β : Coalgebra h)(η : Coalgebra k)
      → Cohomomorphism β η → Cohomomorphism α β → Cohomomorphism α η
    compCohomo α β η ϕ ψ .fst a = ϕ .fst a ∘g ψ .fst a
    compCohomo α β η ϕ ψ .snd a =
      cong (_∘g ψ .fst a) (ϕ .snd a)
      ∙ cong ((map (F a) (ϕ .fst)) ∘g_) (ψ .snd a)
      ∙ cong (_∘g α a) (sym (map-∘ (F a) (ϕ .fst) (ψ .fst)))

    module _ {g : A → Grammar ℓ'} (α : Coalgebra g) where
      {-# TERMINATING #-}
      corecCohomo : Cohomomorphism α terminalCoalgebra
      corecCohomo .fst a w x .unrollν = map (F a) (corecCohomo .fst) w (α a w x)
      corecCohomo .snd a = refl

      corec : ∀ a → g a ⊢ (ν F a)
      corec = corecCohomo .fst

    rollν : ∀ a → ⟦ F a ⟧ (ν F) ⊢ ν F a
    rollν a w x .unrollν = x

    rollν' : ∀ a → ⟦ F a ⟧ (ν F) ⊢ ν F a
    rollν' = corec coalg
      where
      coalg : Coalgebra λ a → ⟦ F a ⟧ (ν F)
      coalg a = map (F a) λ a' → unrollν' F a'
