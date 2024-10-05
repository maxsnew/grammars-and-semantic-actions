{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Cubes.Base

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Empty as Empty hiding (⊥;⊥*)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Negation Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.String Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ ℓ' ℓg ℓh ℓk ℓl ℓS : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open isStrongEquivalence

-- A grammar is unambiguous if there is at most one term from any
-- other fixed grammar into it
unambiguous : Grammar ℓg → Typeω
unambiguous g = ∀ {ℓh} {h : Grammar ℓh} → (e e' : h ⊢ g) → e ≡ e'

-- A grammar is unambiguous if it is subterminal ---
-- if the unique map to the terminal object (⊤) is a
-- monomorphism
unambiguous' : Grammar ℓg → Typeω
unambiguous' {ℓg = ℓg} g = isMono {g = g}{h = ⊤} (⊤-intro {g = g})

unambiguous'→unambiguous : unambiguous' g → unambiguous g
unambiguous'→unambiguous unambig e e' =
  unambig e e'
    (sym (is-terminal-⊤ .snd (⊤-intro ∘g e)) ∙
         is-terminal-⊤ .snd (⊤-intro ∘g e') )

unambiguous→unambiguous' : unambiguous g → unambiguous' g
unambiguous→unambiguous' unambig e e' ≡! = unambig e e'

-- A third notion of unambiguity.
-- This is the definition you'd expect in the grammar model of the
-- theory, that each string has at most one parse (up to paths bw parses)
--
-- These definitions should not be used for abstract grammars, but can prove
-- useful for showing unambiguity for things like literals, ε, and string
module EXTERNAL where
  propParses : Grammar ℓg → Type ℓg
  propParses g = ∀ w → isProp (g w)

  propParses→unambiguous' : propParses g → unambiguous' g
  propParses→unambiguous' {g = g} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    opaque
      unfolding uniquely-supported-⌈w⌉ internalize ⊤
      unambiguous'→propParses : unambiguous' g → propParses g
      unambiguous'→propParses {g = g} unambig w pg pg' =
        isMono→injective unambig w pg pg' refl
        where
        pick-parse : ∀ w' (h : Grammar ℓh) → h w' → ⌈ w' ⌉ ⊢ h
        pick-parse w' h p w'' x =
          subst h (uniquely-supported-⌈w⌉ isFinSetAlphabet w' w'' x) p

        isMono→injective : {e : h ⊢ ⊤} →
          isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
        isMono→injective {h = h}{e = e} mono-e w p p' ewp≡ewp' =
          sym (transportRefl p) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p) (isSetString _ w refl _) ∙
          funExt⁻
            (funExt⁻ (mono-e (pick-parse w h p) (pick-parse w h p') refl) w)
              (internalize w) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p') (isSetString _ w _ refl) ∙
          transportRefl p'

    unambigous→propParses : unambiguous g → propParses g
    unambigous→propParses unambig =
      unambiguous'→propParses (unambiguous→unambiguous' unambig)

    propParses→unambiguous : propParses g → unambiguous g
    propParses→unambiguous ppg =
      unambiguous'→unambiguous (propParses→unambiguous' ppg)

totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

open StrongEquivalence

opaque
  unfolding ⊤-intro
  totallyParseable→unambiguous' :
    totallyParseable g → unambiguous' g
  totallyParseable→unambiguous' parseable =
    Mono∘g ⊕-inl _
      (isStrongEquivalence→isMono
        (parseable .snd .fun)
        (StrongEquivalence→isStrongEquivalence _ _ (parseable .snd)))
      isMono-⊕-inl
totallyParseable→unambiguous :
  totallyParseable g → unambiguous g
totallyParseable→unambiguous parseable =
  unambiguous'→unambiguous (totallyParseable→unambiguous' parseable)

decidable : Grammar ℓg → Type ℓg
decidable g = StrongEquivalence (g ⊕ (¬ g)) ⊤

decidable→totallyParseable :
  decidable g → totallyParseable g
decidable→totallyParseable dec-g = _ , dec-g

isUnambiguousRetract :
  ∀ (f : g ⊢ h) (f' : h ⊢ g)
  → (f' ∘g f ≡ id)
  → unambiguous h → unambiguous g
isUnambiguousRetract f f' ret unambH e e' =
  cong (_∘g e) (sym ret)
  ∙ cong (f' ∘g_) (unambH _ _)
  ∙ cong (_∘g e') ret

unambiguous≅ : StrongEquivalence g h → unambiguous g → unambiguous h
unambiguous≅ g≅h unambG = isUnambiguousRetract (g≅h .inv) (g≅h .fun) (g≅h .sec) unambG
  where open isStrongEquivalence

unambiguous→StrongEquivalence
  : unambiguous g
  → unambiguous h
  → (g ⊢ h)
  → (h ⊢ g)
  → StrongEquivalence g h
unambiguous→StrongEquivalence unambG unambH f f' =
  mkStrEq f f' (unambH (f ∘g f') id) (unambG (f' ∘g f) id)

unambiguousRetract→StrongEquivalence
  : ∀ (f : g ⊢ h) (f' : h ⊢ g)
  → (f' ∘g f ≡ id)
  → unambiguous h
  → StrongEquivalence g h
unambiguousRetract→StrongEquivalence f f' ret unambH
  = unambiguous→StrongEquivalence (isUnambiguousRetract f f' ret unambH) unambH f f'
