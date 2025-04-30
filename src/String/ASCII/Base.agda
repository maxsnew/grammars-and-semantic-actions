{-# OPTIONS --erased-cubical #-}
-- Subset of ASCII characters for writing test cases
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.ASCII.Base where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Erased.Relation.Nullary.Base

open import Erased.Data.SumFin.Base
open import Erased.Data.SumFin.Properties
open import Erased.Data.FinSet.Base
open import Erased.Data.FinSet.Properties
open import Erased.Data.Nat.Base
-- open import Cubical.Data.Nat.Order
open import Erased.Data.Maybe.Base
open import Erased.Data.Sigma.Base
-- import Cubical.Data.Empty as Empty
open import Erased.Data.List as List
-- open import Cubical.Data.List.FinData
import Cubical.Data.Equality as Eq

open import String.Unicode

open import Agda.Builtin.String using (primShowChar)

private
  variable
    ℓ' ℓ'' : Level

-- Enough of the ASCII table for nice tests
-- TODO : go back and make this the whole table
opaque
  ASCIIChar : Type
  ASCIIChar = Fin 97

  SPACE NEWLINE TAB EXLCAM POUND SINGLEQUOTE DOUBLEQUOTE
    DOLLAR PERCENT AMPERSAND LPAREN RPAREN ASTERISK
    PLUS COMMA MINUS PERIOD FSLASH BSLASH COLON SEMICOLON
    GT EQ LT QUESTION AT LBRACKET RBRACKET CARROT UNDERSCORE
    BACKTICK TILDE LCURLY RCURLY VERTBAR A^ B^
    C^ D^ E^ F^ G^ H^ I^ J^ K^ L^ M^
    N^ O^ P^ Q^ R^ S^ T^ U^ V^ W^ X^ Y^
    Z^ a^ b^ c^ d^ e^ f^ g^ h^ i^ j^ k^ l^ m^ n^ o^ p^ q^ r^
    s^ t^ u^ v^ w^ x^ y^ z^
    zero^ one^ two^ three^ four^ five^
    six^ seven^ eight^ nine^ : ASCIIChar

  SPACE =       fromℕ {k = 96} 0
  NEWLINE =     fromℕ {k = 96} 1
  TAB =         fromℕ {k = 96} 2
  EXLCAM =      fromℕ {k = 96} 3
  POUND =       fromℕ {k = 96} 4
  SINGLEQUOTE = fromℕ {k = 96} 5
  DOUBLEQUOTE = fromℕ {k = 96} 6
  DOLLAR =      fromℕ {k = 96} 7
  PERCENT =     fromℕ {k = 96} 8
  AMPERSAND =   fromℕ {k = 96} 9
  LPAREN =      fromℕ {k = 96} 10
  RPAREN =      fromℕ {k = 96} 11
  ASTERISK =    fromℕ {k = 96} 12
  PLUS =        fromℕ {k = 96} 13
  COMMA =       fromℕ {k = 96} 14
  MINUS =       fromℕ {k = 96} 15
  PERIOD =      fromℕ {k = 96} 16
  FSLASH =      fromℕ {k = 96} 17
  BSLASH =      fromℕ {k = 96} 18
  COLON =       fromℕ {k = 96} 19
  SEMICOLON =   fromℕ {k = 96} 20
  GT =          fromℕ {k = 96} 21
  EQ =          fromℕ {k = 96} 22
  LT =          fromℕ {k = 96} 23
  QUESTION =    fromℕ {k = 96} 24
  AT =          fromℕ {k = 96} 25
  LBRACKET =    fromℕ {k = 96} 26
  RBRACKET =    fromℕ {k = 96} 27
  CARROT =      fromℕ {k = 96} 28
  UNDERSCORE =  fromℕ {k = 96} 29
  BACKTICK =    fromℕ {k = 96} 30
  TILDE =       fromℕ {k = 96} 31
  LCURLY =      fromℕ {k = 96} 32
  RCURLY =      fromℕ {k = 96} 33
  VERTBAR =     fromℕ {k = 96} 34
  A^ =          fromℕ {k = 96} 35
  B^ =          fromℕ {k = 96} 36
  C^ =          fromℕ {k = 96} 37
  D^ =          fromℕ {k = 96} 38
  E^ =          fromℕ {k = 96} 39
  F^ =          fromℕ {k = 96} 40
  G^ =          fromℕ {k = 96} 41
  H^ =          fromℕ {k = 96} 42
  I^ =          fromℕ {k = 96} 43
  J^ =          fromℕ {k = 96} 44
  K^ =          fromℕ {k = 96} 45
  L^ =          fromℕ {k = 96} 46
  M^ =          fromℕ {k = 96} 47
  N^ =          fromℕ {k = 96} 48
  O^ =          fromℕ {k = 96} 49
  P^ =          fromℕ {k = 96} 50
  Q^ =          fromℕ {k = 96} 51
  R^ =          fromℕ {k = 96} 52
  S^ =          fromℕ {k = 96} 53
  T^ =          fromℕ {k = 96} 54
  U^ =          fromℕ {k = 96} 55
  V^ =          fromℕ {k = 96} 56
  W^ =          fromℕ {k = 96} 57
  X^ =          fromℕ {k = 96} 58
  Y^ =          fromℕ {k = 96} 59
  Z^ =          fromℕ {k = 96} 60
  a^ =          fromℕ {k = 96} 61
  b^ =          fromℕ {k = 96} 62
  c^ =          fromℕ {k = 96} 63
  d^ =          fromℕ {k = 96} 64
  e^ =          fromℕ {k = 96} 65
  f^ =          fromℕ {k = 96} 66
  g^ =          fromℕ {k = 96} 67
  h^ =          fromℕ {k = 96} 68
  i^ =          fromℕ {k = 96} 69
  j^ =          fromℕ {k = 96} 70
  k^ =          fromℕ {k = 96} 71
  l^ =          fromℕ {k = 96} 72
  m^ =          fromℕ {k = 96} 73
  n^ =          fromℕ {k = 96} 74
  o^ =          fromℕ {k = 96} 75
  p^ =          fromℕ {k = 96} 76
  q^ =          fromℕ {k = 96} 77
  r^ =          fromℕ {k = 96} 78
  s^ =          fromℕ {k = 96} 79
  t^ =          fromℕ {k = 96} 80
  u^ =          fromℕ {k = 96} 81
  v^ =          fromℕ {k = 96} 82
  w^ =          fromℕ {k = 96} 83
  x^ =          fromℕ {k = 96} 84
  y^ =          fromℕ {k = 96} 85
  z^ =          fromℕ {k = 96} 86
  zero^ =       fromℕ {k = 96} 87
  one^ =        fromℕ {k = 96} 88
  two^ =        fromℕ {k = 96} 89
  three^ =      fromℕ {k = 96} 90
  four^ =       fromℕ {k = 96} 91
  five^ =       fromℕ {k = 96} 92
  six^ =        fromℕ {k = 96} 93
  seven^ =      fromℕ {k = 96} 94
  eight^ =      fromℕ {k = 96} 95
  nine^ =       fromℕ {k = 96} 96

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
  ('y' , y^) ∷ ('z' , z^) ∷ ('0' , zero^) ∷
  ('1' , one^) ∷ ('2' , two^) ∷ ('3' , three^) ∷
  ('4' , four^) ∷ ('5' , five^) ∷ ('6' , six^) ∷
  ('7' , seven^) ∷ ('8' , eight^) ∷ ('9' , nine^) ∷
  []

@0 _ : 97 ≡ length translation
_ = refl

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  (discA : DecEq A) where
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

-- Unicode→ASCII : UnicodeChar → Maybe ASCIIChar
-- Unicode→ASCII = find {!!} translation

opaque
  unfolding ASCIIChar
  ASCII→Unicode' : ASCIIChar → Maybe UnicodeChar
  ASCII→Unicode' = find (decEqFin 97) (map (λ (u , a) → (a , u)) translation)

ASCII→UnicodeChar : ASCIIChar → UnicodeChar
ASCII→UnicodeChar c = rec '🅱' (λ x → x) (ASCII→Unicode' c)

ASCII→UnicodeString : ASCIIChar → UnicodeString
ASCII→UnicodeString c = primShowChar (ASCII→UnicodeChar c)

opaque
  unfolding ASCIIChar
  @0 isSetASCIIChar : isSet ASCIIChar
  isSetASCIIChar = isSetFin {k = 97}

open IsoEq
opaque
  unfolding ASCIIChar
  isFinOrd'ASCII : isFinOrd' ASCIIChar
  isFinOrd'ASCII .fst = length translation
  isFinOrd'ASCII .snd .fun x = x
  isFinOrd'ASCII .snd .inv x = x
  isFinOrd'ASCII .snd .rightInv _ = Eq.refl
  isFinOrd'ASCII .snd .leftInv _ = Eq.refl

decEqASCII : DecEq ASCIIChar
decEqASCII = isFinOrd'→DecEq isFinOrd'ASCII

--   @0 isFinSetASCII : isFinSet ASCIIChar
--   isFinSetASCII = isFinSetFin {n = 97}

-- DiscreteASCII : Discrete ASCIIChar
-- DiscreteASCII = isFinSet→Discrete isFinSetASCII

-- ASCII : hSet ℓ-zero
-- ASCII = ASCIIChar , isSetASCII
