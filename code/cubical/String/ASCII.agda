-- Subset of ASCII characters for writing test cases
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.ASCII where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Fin
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.List as List
open import Cubical.Data.List.FinData


private
  variable
    ℓ' ℓ'' : Level

data ASCIIChar : Type ℓ-zero where
  SPACE NEWLINE TAB EXLCAM POUND
    SINGLEQUOTE DOUBLEQUOTE DOLLAR PERCENT
    AMPERSAND LPAREN RPAREN ASTERISK PLUS COMMA
    MINUS PERIOD FSLASH BSLASH COLON SEMICOLON
    GT EQ LT QUESTION AT LBRACKET RBRACKET CARROT
    UNDERSCORE BACKTICK TILDE LCURLY RCURLY VERTBAR
    A^ B^ C^ D^ E^ F^ G^ H^ I^ J^ K^ L^ M^
    N^ O^ P^ Q^ R^ S^ T^ U^ V^ W^ X^ Y^ Z^
    a^ b^ c^ d^ e^ f^ g^ h^ i^ j^ k^ l^ m^
    n^ o^ p^ q^ r^ s^ t^ u^ v^ w^ x^ y^ z^
    : ASCIIChar
  isSetASCIIChar :
    ∀ (c c' : ASCIIChar) (p q : c ≡ c') → p ≡ q

ASCII : hSet ℓ-zero
ASCII = ASCIIChar , isSetASCIIChar

open import String.Unicode
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

translation : List (UnicodeChar × ASCIIChar)
translation =
  (' ' , SPACE) ∷ ('\n' , NEWLINE) ∷ ('\t' , TAB) ∷
  ('!' , EXLCAM) ∷ ('#' , POUND) ∷
  ('\'' , SINGLEQUOTE) ∷ ('"' , DOUBLEQUOTE) ∷
  ('$' , DOLLAR) ∷ ('%' , PERCENT) ∷
  ('&' , AMPERSAND) ∷ ('(' , LPAREN) ∷
  (')' , RPAREN) ∷ ('*' , ASTERISK) ∷
  ('+' , PLUS) ∷ (',' , COMMA) ∷ ('-' , MINUS) ∷
  ('.' , PERIOD) ∷ ('/' , FSLASH) ∷
  ('\\' , BSLASH) ∷ (':' , COLON) ∷
  (';' , SEMICOLON) ∷ ('>' , GT) ∷ ('=' , EQ) ∷
  ('<' , LT) ∷ ('?' , QUESTION) ∷ ('@' , AT) ∷
  ('[' , LBRACKET) ∷ (']' , RBRACKET) ∷
  ('^' , CARROT) ∷ ('_' , UNDERSCORE) ∷
  ('`' , BACKTICK) ∷ ('~' , TILDE) ∷
  ('{' , LCURLY) ∷ ('}' , RCURLY) ∷
  ('|' , VERTBAR) ∷ ('A' , A^) ∷ ('B' , B^) ∷
  ('C' , C^) ∷ ('D' , D^) ∷ ('E' , E^) ∷
  ('F' , F^) ∷ ('G' , G^) ∷ ('H' , H^) ∷
  ('I' , I^) ∷ ('J' , J^) ∷ ('K' , K^) ∷
  ('L' , L^) ∷ ('M' , M^) ∷ ('N' , N^) ∷
  ('O' , O^) ∷ ('P' , P^) ∷ ('Q' , Q^) ∷
  ('R' , R^) ∷ ('S' , S^) ∷ ('T' , T^) ∷
  ('U' , U^) ∷ ('V' , V^) ∷ ('W' , W^) ∷
  ('X' , X^) ∷ ('Y' , Y^) ∷ ('Z' , Z^) ∷
  ('a' , a^) ∷ ('b' , b^) ∷ ('c' , c^) ∷
  ('d' , d^) ∷ ('e' , e^) ∷ ('f' , f^) ∷
  ('g' , g^) ∷ ('h' , h^) ∷ ('i' , i^) ∷
  ('j' , j^) ∷ ('k' , k^) ∷ ('l' , l^) ∷
  ('m' , m^) ∷ ('n' , n^) ∷ ('o' , o^) ∷
  ('p' , p^) ∷ ('q' , q^) ∷ ('r' , r^) ∷
  ('s' , s^) ∷ ('t' , t^) ∷ ('u' , u^) ∷
  ('v' , v^) ∷ ('w' , w^) ∷ ('x' , x^) ∷
  ('y' , y^) ∷ ('z' , z^) ∷ []

-- TODO move this
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  (discA : Discrete A) where
  find : List (A × B) → (a : A) → Maybe B
  find [] the-a = nothing
  find ((a' , b') ∷ abs) the-a =
    decRec
      (λ _ → just b')
      (λ _ → find abs the-a)
      (discA a' the-a)

  findIdx : List (A × B) → (a : A) → ℕ → Maybe ℕ
  findIdx [] the-a n = nothing
  findIdx ((a' , b') ∷ abs) the-a n =
    decRec
      (λ _ → just n)
      (λ _ → findIdx abs the-a (suc n))
      (discA a' the-a)

Unicode→ASCII : UnicodeChar → Maybe ASCIIChar
Unicode→ASCII = find DiscreteUnicodeChar translation

postulate
  isFinSetASCIIChar : isFinSet ASCIIChar
-- isFinSetASCIIChar = EquivPresIsFinSet {!!} {!!}

DiscreteASCIIChar : Discrete ASCIIChar
DiscreteASCIIChar = isFinSet→Discrete isFinSetASCIIChar
