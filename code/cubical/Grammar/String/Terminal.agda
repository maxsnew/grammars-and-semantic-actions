open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Terminal (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Unambiguous Alphabet
open import Grammar.Equivalence.Base Alphabet

open import Term.Base Alphabet

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
read w _ = ⌈w⌉→string {w = w} w (internalize w)

read' : ⊤ ⊢ string
read' w _ = mkstring' w

read* : ∀ {ℓA} → ⊤* {ℓA} ⊢ string
read* w _ = ⌈w⌉→string {w = w} w (internalize w)

string≅stringL : string ≅ stringL
string≅stringL = *≅*L char

string-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ string
string-intro = read ∘g ⊤-intro

stringL-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ stringL
stringL-intro = string≅stringL .fun ∘g string-intro

string≅⊤ : string ≅ ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = read
string≅⊤ .sec = unambiguous⊤ _ _
string≅⊤ .ret = unambiguous-string _ _

