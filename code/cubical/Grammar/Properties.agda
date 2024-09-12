open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Properties (Alphabet : hSet ℓ-zero) where

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

totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

open StrongEquivalence

totallyParseable→unambiguous :
  totallyParseable g → unambiguous g
totallyParseable→unambiguous parseable =
  Mono∘g (isStrongEquivalence→isMono {!!} {!parseable .snd !}) {!!}

decidable : Grammar ℓg → Type ℓg
decidable g = StrongEquivalence (g ⊕ (¬ g)) ⊤

unambiguous⊤ : unambiguous ⊤
unambiguous⊤ e e' _ = refl

unambiguous⊤* : ∀ {ℓg} → unambiguous (⊤* {ℓg})
unambiguous⊤* e e' _ = refl

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ {k = k} e e' !∘e≡!∘e' =
  is-initial→propHoms (g⊢⊥→is-initial e) _ _

