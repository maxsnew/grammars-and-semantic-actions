open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module ParserCombinator.Base (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Equality as Eq
open import Cubical.Data.List using ([])
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary.Base renaming (Dec to NLDec; decRec to nlDecRec)

open import Grammar Alphabet as Grammar hiding (char)
open import Grammar.Inductive.Indexed Alphabet hiding (map)
open import Grammar.Equivalence Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Maybe Alphabet as Maybe
open import Term Alphabet

private
  variable
    ℓ ℓg : Level
    g h l : Grammar _

WeakParser : (g : Grammar ℓg) → Type ℓg
WeakParser g = string ⊢ Maybe (g ⊗ string)

FinishedWeakParser : (g : Grammar ℓg) → Type ℓg
FinishedWeakParser g = string ⊢ Maybe g

finish : WeakParser g → FinishedWeakParser g
finish x =
  Maybe.μ
  ∘g fmap
    (fmap ⊗-unit*-r
    ∘g Maybe⊗r
    ∘g ⊗-intro id (fold*r _ λ _ → ⊕ᴰ-elim (λ where
      nil → just ∘g lowerG
      cons → nothing)))
  ∘g x

pure : Element g → WeakParser g
pure x = just ∘g ⊗-intro (ε-elim x) id ∘g ⊗-unit-l⁻

map : g ⊢ h → WeakParser g → WeakParser h
map f x = fmap (⊗-intro f id) ∘g x

mapMaybe : g ⊢ Maybe h → WeakParser g → WeakParser h
mapMaybe f x = Maybe.μ ∘g fmap (Maybe⊗l ∘g ⊗-intro f id) ∘g x

concat : WeakParser g → WeakParser h → WeakParser (g ⊗ h)
concat x y = Maybe.μ ∘g fmap (fmap ⊗-assoc ∘g Maybe⊗r ∘g ⊗-intro id y) ∘g x

infixr 5 _<⊗>_
_<⊗>_ = concat

fail : WeakParser g
fail = nothing

infixr 5 _<|>_
_<|>_ : WeakParser g → WeakParser h → WeakParser (g ⊕ h)
x <|> y = ⊕-elim (just ∘g ⊗-intro ⊕-inl id) (fmap (⊗-intro ⊕-inr id) ∘g y ∘g ⊤*→string) ∘g x

-- TODO: address nontermination when `g` admits `ε`
{-# NON_TERMINATING #-}
many : WeakParser g → WeakParser (g *)
many x = Maybe.μ ∘g fmap (fmap (⊗-intro CONS id ∘g ⊗-assoc) ∘g Maybe⊗r ∘g ⊗-intro id (many x)) ∘g x

rest : WeakParser string
rest = just ∘g ⊗-intro id (⊤→string ∘g ⊤-intro) ∘g ⊗-unit-r⁻

anyChar : WeakParser Grammar.char
anyChar = ⊕ᴰ-elim (λ where
    nil → nothing
    cons → just ∘g ⊗-intro lowerG (⊤→string ∘g ⊤-intro))
  ∘g unroll _ _

satisfy :
  {P : ⟨ Alphabet ⟩ → Type ℓ}
  (P-dec : (c : ⟨ Alphabet ⟩) → NLDec (P c)) →
  WeakParser (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ p ∈ P c ] literal c)
satisfy P-dec = mapMaybe
  (⊕ᴰ-elim (λ c → nlDecRec
    (λ p → just ∘g ⊕ᴰ-in c ∘g ⊕ᴰ-in p)
    (λ _ → nothing)
    (P-dec c)))
  anyChar

module _ (decEq : Discrete ⟨ Alphabet ⟩) where

  char : (c : ⟨ Alphabet ⟩) → WeakParser (literal c)
  char c = map
    (⊕ᴰ-elim (λ c' → ⊕ᴰ-elim (J (λ c' p → literal c' ⊢ literal c) id)))
    (satisfy (decEq c))

