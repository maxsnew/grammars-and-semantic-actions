open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Top.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Top.Base Alphabet
open import Term.Base Alphabet

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
