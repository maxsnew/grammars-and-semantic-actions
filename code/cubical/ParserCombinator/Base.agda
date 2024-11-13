open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module ParserCombinator.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List using ([])
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary.Base renaming (Dec to NLDec; decRec to nlDecRec)

open import Grammar Alphabet as Grammar hiding (char)
open import Grammar.Inductive.Indexed Alphabet hiding (map)
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.String.Properties Alphabet
open import SemanticAction.Base Alphabet
open import SemanticAction.Length Alphabet
open import Term Alphabet

private
  variable
    ℓ ℓg : Level
    g h l : Grammar _

WeakParserG : (g : Grammar ℓg) → Grammar ℓg
WeakParserG g = ((g ⊗ string) ⊕ ⊤) ⟜ string

WeakParser : (g : Grammar ℓg) → Type ℓg
WeakParser g = string ⊢ (g ⊗ string) ⊕ ⊤

pure : (g ⊢ h) → (g ⊢ WeakParserG h)
pure x = ⟜-intro (⊕-inl ∘g ⊗-intro x id)

pure' : Element g → WeakParser g
pure' x = ⊕-inl ∘g ⊗-intro (ε-elim x) id ∘g ⊗-unit-l⁻

fail : g ⊢ WeakParserG h
fail = ⟜-intro (⊕-inr ∘g ⊤-intro)

fail' : WeakParser g
fail' = ⊕-inr ∘g ⊤-intro

bind : (l ⊢ WeakParserG g) → (g ⊢ WeakParserG h) → (l ⊢ WeakParserG h)
bind x y = ⟜-intro (⊕-elim (⟜-app ∘g ⊗-intro y id) (⊕-inr ∘g ⊤-intro) ∘g ⟜-app) ∘g x

_>>=_ : (l ⊢ WeakParserG g) → (g ⊢ WeakParserG h) → (l ⊢ WeakParserG h)
_>>=_ = bind

bind' : WeakParser g → (Element g → WeakParser h) → WeakParser h
bind' x f = ⊕-elim {!!} (⊕-inr ∘g id) ∘g x

map : (g ⊢ h) → (l ⊢ WeakParserG g) → (l ⊢ WeakParserG h)
map f x = bind x (pure f)

concat : (l ⊢ WeakParserG g) → (ε ⊢ WeakParserG h) → (l ⊢ WeakParserG (g ⊗ h))
concat x y =
  x
  >>= ({!!} ∘g ⊗-intro id y ∘g ⊗-unit-r⁻)


anyChar : ε ⊢ WeakParserG Grammar.char
anyChar = ⟜-intro-ε (⊕ᴰ-elim (λ where
    nil → ⟜-elim-ε fail ∘g ⊤→string ∘g ⊤-intro
    cons → ⊕-inl ∘g ⊗-intro lowerG (⊤→string ∘g ⊤-intro))
  ∘g unroll _ _)

satisfy :
  {P : ⟨ Alphabet ⟩ → Type ℓ}
  (P-dec : (c : ⟨ Alphabet ⟩) → NLDec (P c)) →
  ε ⊢ WeakParserG (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ p ∈ P c ] literal c)
satisfy P-dec =
  anyChar
  >>= (⊕ᴰ-elim (λ c → nlDecRec
    (λ p → pure (⊕ᴰ-in c ∘g ⊕ᴰ-in p))
    (λ _ → fail)
    (P-dec c)))

module _ (decEq : Discrete ⟨ Alphabet ⟩) where

  char : (c : ⟨ Alphabet ⟩) → ε ⊢ WeakParserG (literal c)
  char c =
    anyChar
    >>= ⊕ᴰ-elim (λ c' → nlDecRec
      (J (λ c' c≡c' → literal c' ⊢ _) (pure id))
      (λ _ → fail)
      (decEq c c'))

