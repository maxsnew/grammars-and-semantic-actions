open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Parser.RecursiveDescent (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Unit

open import Grammar Alphabet
open import Grammar.Maybe.Base Alphabet
open import Grammar.External.String.Tiny Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Term Alphabet

open StrongEquivalence

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

MaybeLeft : Grammar ℓA → Grammar ℓA
MaybeLeft A = Maybe (A ⊗ string)

Parser : Grammar ℓA → Type ℓA
Parser A = string ⊢ MaybeLeft A

onSuccess : (A ⊗ string ⊢ MaybeLeft B) → MaybeLeft A ⊢ MaybeLeft B
onSuccess = λ k → ⊕-elim k nothing

mapResult : A ⊢ B → MaybeLeft A ⊢ MaybeLeft B
mapResult f = fmap (f ,⊗ id)

seqP : Parser A → Parser B → Parser (A ⊗ B)
seqP p q = onSuccess (fmap ⊗-assoc ∘g Maybe⊗r ∘g id ,⊗ q) ∘g p

anyChar : Parser char
anyChar = ⊕-elim nothing just ∘g unroll-string≅ .fun

requireEnd : MaybeLeft A ⊢ Maybe A
requireEnd =
  ⊕-elim
    (⊕-elim (just ∘g ⊗-unit-r) nothing
      ∘g ⊗⊕-distL
      ∘g id ,⊗ unroll-string≅ .fun)
    nothing

parse : Parser A → string ⊢ Maybe A
parse p = requireEnd ∘g p

fixP : ▷ (MaybeLeft A) ⊢ MaybeLeft A → Parser A
fixP body = lob body ∘g ⊤-intro

fixPr : ▷r (MaybeLeft A) ⊢ MaybeLeft A → Parser A
fixPr body = lob-r body ∘g ⊤-intro

opaque
  unfolding unfoldGrammarDefs unfoldParserDefs lob lob-r

  unfoldRecursiveDescentDefs : Unit
  unfoldRecursiveDescentDefs = tt
