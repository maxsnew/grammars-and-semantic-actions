open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.HLevels.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet

open import Grammar Alphabet
open import Term Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

-- This is the definition of unambiguity you'd expect in the grammar model of the
-- theory, that each string has at most one parse (up to paths bw parses)
--
-- These definitions should not be used for abstract grammars, but can prove
-- useful for showing unambiguity for things like literals, ε, and string
module EXTERNAL where
  isLang→unambiguous' : isLang g → unambiguous' g
  isLang→unambiguous' {g = g} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  opaque
    unfolding ⊤
    isMono→injective : {e : h ⊢ ⊤} →
      isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
    isMono→injective {h = h}{e = e} mono-e w p p' ewp≡ =
      sym (transportRefl p)
      ∙ cong (λ a → transp (λ i → h (a i)) i0 p) (isSetString _ w refl _)
      ∙ funExt⁻ (funExt⁻ (mono-e (pick-parse w h p) (pick-parse w h p') refl) w) (internalize w)
      ∙ cong (λ a → transp (λ i → h (a i)) i0 p') (isSetString _ w _ refl)
      ∙ transportRefl p'

  opaque
    unfolding ⊤
    unambiguous'→isLang : unambiguous' g → isLang g
    unambiguous'→isLang {g = g} unambig w pg pg' =
      isMono→injective {e = ⊤-intro} unambig w pg pg' refl

    unambiguous→isLang : unambiguous g → isLang g
    unambiguous→isLang unambig =
      unambiguous'→isLang (unambiguous→unambiguous' unambig)

    isLang→unambiguous : isLang g → unambiguous g
    isLang→unambiguous ppg =
      unambiguous'→unambiguous (isLang→unambiguous' ppg)
