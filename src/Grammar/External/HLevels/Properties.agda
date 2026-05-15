open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

module Grammar.External.HLevels.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Functions.Embedding

open import Cubical.Data.FinSet
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

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
isLang→unambiguous' : isLang A → unambiguous' A
isLang→unambiguous' {A = A} unambig' e e' _ =
  funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

opaque
  unfolding ⊤
  -- Post-merge `pick-parse` lands in the Eq-world via
  --   pick-parse w A x w (mk⌈⌉ w) = Eq.transport A (uniquely-supported-⌈⌉Eq w w (mk⌈⌉ w)) x.
  -- The internal Eq-proof inhabits `w Eq.≡ w`, which is propositional, so
  -- it agrees with `Eq.refl` and the whole transport is the identity. We
  -- stay in Eq world by moving along that proof-irrelevance path; no
  -- cubical `transp` / `subst` is needed on the witness.
  isMono⊤→injective : {e : B ⊢ ⊤} →
    isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
  isMono⊤→injective {B = B}{e = e} mono-e w p p' ewp≡ =
    cong (λ q → Eq.transport B q p) (isSetEqString w w Eq.refl _)
    ∙ funExt⁻ (funExt⁻ (mono-e (pick-parse w B p) (pick-parse w B p') refl) w) (mk⌈⌉ w)
    ∙ cong (λ q → Eq.transport B q p') (isSetEqString w w _ Eq.refl)

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
