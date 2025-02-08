open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

module Grammar.Subgrammar.Examples (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.HLevels.MonoInjective Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)

open import Grammar.Subgrammar.Base Alphabet
open import Grammar.String.Properties Alphabet

open import Cubical.HITs.PropositionalTruncation

open import Term Alphabet

open StrongEquivalence

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open Subgrammar

-- Testing to see if I can define "starts with c"
-- as a subgrammar
module _
  (g : Grammar ℓg)
  (c : ⟨ Alphabet ⟩)
  where
  startsWith : Grammar ℓg
  startsWith = g & (＂ c ＂ ⊗ ⊤)

  startsWith' : Grammar ℓg
  startsWith' = preimage {ℓ = ℓg} (&-π₁ {g = g}{h = ＂ c ＂ ⊗ ⊤} ) (true ∘g ⊤-intro)

  _ : startsWith' ⊢ startsWith
  _ = sub-π (true ∘g ⊤-intro ∘g &-π₁)

  _ : startsWith ⊢ startsWith'
  _ = sub-intro (true ∘g ⊤-intro ∘g &-π₁) id (cong (true ∘g_) (unambiguous⊤ _ _))



-- Does not witness a follow last with c as the following
-- character
module _
  (g : Grammar ℓg)
  (unambig : unambiguous g)
  (isSetGrammar-g : isSetGrammar g)
  (c : ⟨ Alphabet ⟩)
  where

  FLG : Grammar ℓg
  FLG = g & (char +) ⊗ ＂ c ＂ ⊗ string

  notFL' : Grammar ℓg
  notFL' = g & ¬G FLG

  notFL : Grammar ℓg
  notFL = preimage {ℓ = ℓg} (&-π₁ {g = g}{h = ¬G FLG}) (true ∘g ⊤-intro)

  _ : {h : Grammar ℓh} → h ⊢ notFL → h & FLG ⊢ ⊥
  _ = λ f →
    ⇒-app
    ∘g &-π₂
    ∘g &-assoc⁻
    ∘g (sub-π (true ∘g ⊤-intro ∘g &-π₁ {g = g}{h = ¬G FLG}) ∘g f) ,&p id

