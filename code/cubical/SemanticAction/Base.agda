{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module SemanticAction.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓS : Level
    A : Type _

Δ : Type ℓS → Grammar ℓS
Δ X = ⊕[ x ∈ X ] ⊤

SemanticAction : Grammar ℓg → Type ℓS → Type _
SemanticAction g X = ε ⊢ (g ⊸ Δ X)

semact-⊕ :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction g A → SemanticAction h A →
  SemanticAction (g ⊕ h) A
semact-⊕ x y = ⊸-intro-ε (⊕-elim
  (⊸-intro⁻ x ∘g ⊗-unit-r⁻)
  (⊸-intro⁻ y ∘g ⊗-unit-r⁻))

semact-underlying :
  {g : Grammar ℓg} →
  SemanticAction g (List ⟨ Alphabet ⟩)
semact-underlying = {!!}

semact-surround :
  {g : Grammar ℓg} {h : Grammar ℓh} {k : Grammar ℓk} →
  SemanticAction h A →
  SemanticAction (g ⊗ h ⊗ k) A
semact-surround x = {!⊗-elim!}

