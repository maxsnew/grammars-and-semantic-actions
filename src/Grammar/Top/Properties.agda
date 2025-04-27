{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Top.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Top.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA

opaque
  unfolding ⊤
  @0 unambiguous'⊤ : unambiguous' ⊤
  unambiguous'⊤ e e' _ = refl

@0 unambiguous⊤ : unambiguous ⊤
unambiguous⊤ = unambiguous'→unambiguous unambiguous'⊤

opaque
  unfolding ⊤*
  @0 unambiguous'⊤* : ∀ {ℓA} → unambiguous' (⊤* {ℓA})
  unambiguous'⊤* e e' _ = refl

@0 unambiguous⊤* : ∀ {ℓA} → unambiguous (⊤* {ℓA})
unambiguous⊤* = unambiguous'→unambiguous unambiguous'⊤*

opaque
  unfolding ⊤
  @0 isLang⊤ : isLang ⊤
  isLang⊤ w x y = refl

@0 isSetGrammar⊤ : isSetGrammar ⊤
isSetGrammar⊤ = isLang→isSetGrammar isLang⊤
