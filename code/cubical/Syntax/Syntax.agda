-- {-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Syntax.Syntax where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
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

module Syntax (Σ₀ : Type) where
  data Grammar : Type
  data StrictlyPositiveGrammar : Type

  data Grammar where
    unit : Grammar
    literal : Σ₀ → Grammar
    _⊗_ : Grammar → Grammar → Grammar
    _⊕_ : Grammar → Grammar → Grammar
    μ : (X : StrictlyPositiveGrammar) → Grammar
    ⊗Assoc : ∀ {g h k} → g ⊗ (h ⊗ k) ≡ (g ⊗ h) ⊗ k

  data StrictlyPositiveGrammar where
    var : StrictlyPositiveGrammar
    _⊗literal_ : StrictlyPositiveGrammar → Σ₀ → StrictlyPositiveGrammar
    _literal⊗_ : Σ₀ → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕literal_ : StrictlyPositiveGrammar → Σ₀ → StrictlyPositiveGrammar
    _literal⊕_ : Σ₀ → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕unit : StrictlyPositiveGrammar → StrictlyPositiveGrammar
    unit⊕_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊗spg_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕spg_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊗l_ : Grammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar

  eval-spg : StrictlyPositiveGrammar → Grammar → Grammar
  eval-spg var g = g
  eval-spg (x ⊗literal c) g =
    eval-spg x g ⊗ literal c
  eval-spg (c literal⊗ x) g =
    literal c ⊗ eval-spg x g
  eval-spg (x ⊕literal c) g =
    eval-spg x g ⊕ literal c
  eval-spg (c literal⊕ x) g =
    literal c ⊕ eval-spg x g
  eval-spg (x ⊕unit) g =
    eval-spg x g ⊕ unit
  eval-spg (unit⊕ x) g =
    unit ⊕ eval-spg x g
  eval-spg (x ⊗spg y) g =
    eval-spg x g ⊗ eval-spg y g
  eval-spg (x ⊕spg y) g =
    eval-spg x g ⊕ eval-spg y g
  eval-spg (x ⊗l y) g = x ⊗ eval-spg y g

  data _⊢_ : List Grammar → Grammar → Type where
    identity : ∀ {g} → [ g ] ⊢ g

    unit-I : [] ⊢ unit
    unit-E : ∀ {Δ Δ₁ Δ₂} {g} →
      Δ ⊢ unit →
      (Δ₁ ++ Δ₂) ⊢ g →
      (Δ₁ ++ Δ ++ Δ₂) ⊢ g

    ⊗-I : ∀ {Δ₁ Δ₂} {g g'} →
      Δ₁ ⊢ g →
      Δ₂ ⊢ g' →
      (Δ₁ ++ Δ₂) ⊢ (g ⊗ g')
    ⊗-E : ∀ {Δ Δ₁ Δ₂} {g g' h} →
      Δ ⊢ (g ⊗ g') →
      (Δ₁ ++ [ g ] ++ [ g' ] ++ Δ₂) ⊢ h →
      (Δ₁ ++ Δ ++ Δ₂) ⊢ h

    ⊕-I₁ : ∀ {Δ} {g g'} →
      Δ ⊢ g →
      Δ ⊢ (g ⊕ g')
    ⊕-I₂ : ∀ {Δ} {g g'} →
      Δ ⊢ g' →
      Δ ⊢ (g ⊕ g')
    ⊕-E : ∀ {Δ} {g g' h} →
      Δ ⊢ (g ⊕ g') →
      [ g ] ⊢ h →
      [ g' ] ⊢ h →
      Δ ⊢ h

    μ-I : ∀ {Δ} {g} →
      Δ ⊢ eval-spg g (μ g) →
      Δ ⊢ μ g
    μ-E : ∀ {Δ} {g} {h} →
      Δ ⊢ μ g →
      [ eval-spg g h ] ⊢ h →
      Δ ⊢ h

  KL* : (g : Grammar) → Grammar
  KL* g = μ (unit⊕ (g ⊗l var))

module _ where
  data αβ : Type where
    a : αβ
    b : αβ
  open Syntax αβ

  g : Grammar
  g = KL* (literal a ⊗ literal b) ⊗ literal a

  test :  foldl (λ l c → literal c ∷ l) [] (a ∷ b ∷ a ∷ b ∷ a ∷ []) ⊢ g
  test =
    ⊗-I
      {Δ₁ = literal a ∷ literal b ∷ literal a ∷ literal b ∷ []}
      {Δ₂ = [ literal a ]}
      (μ-I
        (⊕-I₂
          (⊗-I
            {Δ₁ = literal a ∷ literal b ∷ []}
            {Δ₂ = literal a ∷ literal b ∷ []}
            (⊗-I identity identity)
            (μ-I
              (⊕-I₂
                (⊗-I
                  {Δ₁ = literal a ∷ literal b ∷ []}
                  {Δ₂ = []}
                  (⊗-I identity identity)
                  (μ-I (⊕-I₁ unit-I))))))))
      identity

