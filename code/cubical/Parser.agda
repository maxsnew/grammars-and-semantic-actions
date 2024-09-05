open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet

module Parser (Alphabet : hSet ℓ-zero)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.Maybe Alphabet
open import Term Alphabet
open import String.More Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

-- Potentially abstraction breaking but seemingly needed. However
-- this is also an axiom we've considered adding
⊤→string : ∀ {ℓg} → Term {ℓg} ⊤-grammar string-grammar
⊤→string w _ = ⌈ w ⌉

Parser : (g : Grammar ℓg) → Type ℓg
Parser g = string-grammar ⊢ Maybe (g ⊗ string-grammar)

is-ε : string-grammar ⊢ Maybe ε-grammar
is-ε = caseKL* char just nothing

-- TODO naming
-- Runs the parser, then only accepts if the parser
-- consumed all of the input string with none leftover
consumes-input : Parser g → string-grammar ⊢ Maybe g
consumes-input parser =
  fmap ⊗-unit-r ∘g
  μ ∘g
  fmap (Maybe⊗r ∘g (⊗-intro id is-ε)) ∘g
  parser

-- Something about a strong monad?
_then_ : Parser g → Parser h → Parser (g ⊗ h)
e then e' =
  fmap ⊗-assoc ∘g
  μ ∘g
  fmap Maybe⊗r ∘g
  fmap (⊗-intro id e') ∘g
  e

-- Try the first parser. If it fails try the second
_or_ : Parser g → Parser g → Parser g
e or e' = ⊕-elim return (e' ∘g ⊤→string) ∘g e

infixr 8 _then_

parseε : Parser ε-grammar
parseε =
  just ∘g
  ⊗-unit-l⁻

parseChar : (c : ⟨ Alphabet ⟩) → Parser (literal c)
parseChar c =
  caseKL* char
    nothing
    (λ _ (split , (c' , lit) , ⌈w⌉) →
      decRec
        (λ c≡c' → just {g = literal c ⊗ string-grammar}
          _ (split ,
             subst (λ a → split .fst .fst ≡ [ a ]) (sym c≡c') lit ,
             ⌈w⌉))
        (λ _ →
          nothing
            {g = char ⊗ string-grammar}
            {h = literal c ⊗ string-grammar}
              _ (split , (c' , lit) , ⌈w⌉))
        (isFinSet→Discrete isFinSetAlphabet c c')
    )
