{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Product Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
-- open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet

open import Term.Base Alphabet
open import Helper

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

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    opaque
      unfolding uniquely-supported-⌈w⌉ internalize ⊤
      unambiguous'→isLang : unambiguous' g → isLang g
      unambiguous'→isLang {g = g} unambig w pg pg' =
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

    unambiguous→isLang : unambiguous g → isLang g
    unambiguous→isLang unambig =
      unambiguous'→isLang (unambiguous→unambiguous' unambig)

    isLang→unambiguous : isLang g → unambiguous g
    isLang→unambiguous ppg =
      unambiguous'→unambiguous (isLang→unambiguous' ppg)

opaque
  unfolding _&_ _⊗_ ε literal
  disjoint-ε-char+ : disjoint ε (char +)
  disjoint-ε-char+ [] (pε , s , (c , pc) , p*) =
    Empty.rec
      (¬cons≡nil (sym (s .snd ∙ cong (_++ s .fst .snd) pc)))
  disjoint-ε-char+ (x ∷ w) (pε , s , pg , p*) =
    Empty.rec (¬cons≡nil pε)

string≅ε⊕char⊗string : string ≅ (ε ⊕ char ⊗ string)
string≅ε⊕char⊗string = {!*≅ε⊕g⊗g*!}
