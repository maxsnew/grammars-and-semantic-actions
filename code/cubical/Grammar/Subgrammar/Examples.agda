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
  private
    p : g ⊢ Ω
    p w x .fst = ∃[ y ∈ (g & (＂ c ＂ ⊗ ⊤)) w ] &-π₁ w y ≡ x
    p w x .snd = isPropPropTrunc
    -- Don't need the PropTrunc if g unambiguous and a SetGrammar

  startsWith : Grammar ℓg
  startsWith = subgrammar p

  startsWith' : Grammar ℓg
  startsWith' = g & (＂ c ＂ ⊗ ⊤)

  -- _ : startsWith ⊢ startsWith'
  -- _ = {!!}

  _ : startsWith' ⊢ startsWith
  _ = sub-intro p &-π₁ (insert-pf p &-π₁ (λ w x → ∣ x , refl ∣₁))


-- Does not start with c
module _
  (g : Grammar ℓg)
  (c : ⟨ Alphabet ⟩)
  where
  private
    p : g ⊢ Ω
    p w x .fst = ∃[ y ∈ (g & ¬G (＂ c ＂ ⊗ ⊤)) w ] &-π₁ w y ≡ x
    p w x .snd = isPropPropTrunc

-- Does not witness a follow last with c as the following
-- character
module _
  (g : Grammar ℓg)
  (unambig : unambiguous g)
  (isSetGrammar-g : isSetGrammar g)
  (c : ⟨ Alphabet ⟩)
  where
  private
    opaque
      unfolding _&_ _⇒_
      p : g ⊢ Ω {ℓ = ℓg}
      p w x .fst =
        Σ[ y ∈ (g & (¬G ((g & (char +)) ⊗ ＂ c ＂ ⊗ string))) w ]
          &-π₁ {g = g}{h = ¬G ((g & (char +)) ⊗ ＂ c ＂ ⊗ string)} w y ≡ x
      p w x .snd =
        isPropΣ
          (isProp×
            (EXTERNAL.unambiguous→isLang unambig w)
            (isProp→ (EXTERNAL.unambiguous→isLang unambiguous⊥ w))
          )
          (λ y → isSetGrammar-g w (&-π₁{g = g}{h = ¬G ((g & (char +)) ⊗ ＂ c ＂ ⊗ string)} w y) x)

      notFL : Grammar ℓg
      notFL = subgrammar p

      -- this is what I'd need for the Kleene star pf
      -- assuming f is built via induction
      test : {h : Grammar ℓh} → h ⊢ notFL → h & ((g & (char +)) ⊗ ＂ c ＂ ⊗ string) ⊢ ⊥
      test f =
        {!!}
        ∘g ({!extract-pf p (sub-π p) (sub-π-pf p)!} ∘g f) ,&p id
