{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels

module Grammar.MonoidalStructure.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List.Base
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A B C D : Grammar ℓA

record MonoidalStr ℓA : Type (ℓ-suc ℓA) where
  field
    ε : Grammar ℓA
    ε-intro : ε []
    ε-elim : ∀ {A : Grammar ℓA} → A [] → ε ⊢ A

    literal : Alphabet → Grammar ℓ-zero
    lit-intro : {c : Alphabet} → literal c [ c ]

    _⊗_ : Grammar ℓA → Grammar ℓA →  Grammar ℓA
    ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
    ⊗-unit-r : A ⊗ ε ⊢ A
    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
    ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)

  _,⊗_ = ⊗-intro
