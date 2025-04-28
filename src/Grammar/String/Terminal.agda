{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Terminal (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Top Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive Alphabet isSetAlphabet
open import Grammar.String.Base Alphabet isSetAlphabet
open import Grammar.String.Unambiguous Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet

open import Term.Base Alphabet isSetAlphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

read : ⊤ ⊢ string
read w _ = mkstring w

@0 read* : ∀ {ℓA} → ⊤* {ℓA} ⊢ string
read* = read ∘g ⊤-intro

-- string≅stringL : string ≅ stringL
-- string≅stringL = *≅*L char

string-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ string
string-intro = read ∘g ⊤-intro

-- stringL-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ stringL
-- stringL-intro = string≅stringL .fun ∘g string-intro

-- This is assumed as an axiom on paper, and
-- it holds semantically
string≅⊤ : string ≅ ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = read
string≅⊤ .sec = unambiguous⊤ _ _
string≅⊤ .ret = unambiguous-string _ _
