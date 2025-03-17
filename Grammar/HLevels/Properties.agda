open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

module Grammar.HLevels.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Functions.Embedding

open import Cubical.Data.FinSet
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Properties Alphabet
open import Term.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- This is the definition of unambiguity you'd expect in the grammar model of the
-- theory, that each string has at most one parse (up to paths bw parses)
--
-- These definitions should not be used for abstract grammars, but can prove
-- useful for showing unambiguity for things like literals, ε, and string
module EXTERNAL where
  isLang→unambiguous' : isLang A → unambiguous' A
  isLang→unambiguous' {A = A} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  opaque
    unfolding ⊤
    isMono⊤→injective : {e : B ⊢ ⊤} →
      isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
    isMono⊤→injective {B = B}{e = e} mono-e w p p' ewp≡ =
      sym (transportRefl p)
      ∙ cong (λ a → transp (λ i → B (a i)) i0 p) (isSetString _ w refl _)
      ∙ funExt⁻ (funExt⁻ (mono-e (pick-parse w B p) (pick-parse w B p') refl) w) (internalize w)
      ∙ cong (λ a → transp (λ i → B (a i)) i0 p') (isSetString _ w _ refl)
      ∙ transportRefl p'

  opaque
    unfolding ⊤
    unambiguous'→isLang : unambiguous' A → isLang A
    unambiguous'→isLang {A = A} unambig w pA pA' =
      isMono⊤→injective {e = ⊤-intro} unambig w pA pA' refl

    unambiguous→isLang : unambiguous A → isLang A
    unambiguous→isLang unambig =
      unambiguous'→isLang (unambiguous→unambiguous' unambig)

    isLang→unambiguous : isLang A → unambiguous A
    isLang→unambiguous ppA =
      unambiguous'→unambiguous (isLang→unambiguous' ppA)
