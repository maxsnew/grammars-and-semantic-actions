open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Negation Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl


open isStrongEquivalence

isStrongEquivalence→isMono :
  (e : g ⊢ h) →
  isStrongEquivalence _ _ e →
  isMono e
isStrongEquivalence→isMono e streq f f' e∘f≡e∘f' =
  cong (_∘g f) (sym (streq .ret)) ∙
  cong (streq .inv ∘g_) e∘f≡e∘f' ∙
  cong (_∘g f') (streq .ret)

Mono∘g : {e : g ⊢ h} {e' : h ⊢ k} →
  isMono e' → isMono e → isMono (e' ∘g e)
Mono∘g {e = e} {e' = e'} mon-e mon-e' f f' e'ef≡e'ef' =
  mon-e' f f' (mon-e (e ∘g f) (e ∘g f') e'ef≡e'ef')

unambiguous : Grammar ℓg → Typeω
unambiguous {ℓg = ℓg} g = isMono {g = g}{h = ⊤} (⊤-intro {g = g})

-- Including this at all is maybe not useful because it is
-- abstraction breaking, but it also grounds the implementation
-- in intuition idk...might delete l8r
-- This is not intended to be used in the library
-- This is the external notion of what we'd expected an unambiguous
-- grammar to be, that each input string is parsed uniquely
unambiguous' : Grammar ℓg → Type ℓg
unambiguous' g = ∀ w → isProp (g w)

-- However the internal notion does subsume the external one
unambiguous'→unambiguous : unambiguous' g → unambiguous g
unambiguous'→unambiguous {g = g} unambig' e e' _ =
  funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

unambiguous→unambiguous' : unambiguous g → unambiguous' g
unambiguous→unambiguous' {g = g} unambig w pg pg' =
  isMono→injective unambig w pg pg' refl
  where
  isMono→injective : {e : h ⊢ k} →
    isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
  isMono→injective {e = e} mono-e w p p' ewp≡ewp' =
    {!mono-e (pick-elt ?) !}

totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

open StrongEquivalence

totallyParseable→unambiguous :
  totallyParseable g → unambiguous g
totallyParseable→unambiguous parseable =
  Mono∘g {e = ⊕-inl}
    (isStrongEquivalence→isMono
      ⊤-intro
      (StrongEquivalence→isStrongEquivalence _ _ (parseable .snd)))
    isMono-⊕-inl

decidable : Grammar ℓg → Type ℓg
decidable g = StrongEquivalence (g ⊕ (¬ g)) ⊤

decidable→totallyParseable :
  decidable g → totallyParseable g
decidable→totallyParseable dec-g = _ , dec-g

unambiguous⊤ : unambiguous ⊤
unambiguous⊤ e e' _ = refl

unambiguous⊤* : ∀ {ℓg} → unambiguous (⊤* {ℓg})
unambiguous⊤* e e' _ = refl

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ {k = k} e e' !∘e≡!∘e' =
  is-initial→propHoms (g⊢⊥→is-initial e) _ _

