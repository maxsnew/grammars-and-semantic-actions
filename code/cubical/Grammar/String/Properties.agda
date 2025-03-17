open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.List.More
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)

open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.Cartesian Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.Cartesian Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Distributivity Alphabet

open import Grammar.String.Base Alphabet
open import Grammar.String.Terminal Alphabet public
open import Grammar.String.Unambiguous Alphabet public
open import Grammar.String.Tiny Alphabet public

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

opaque
  unfolding _&_ _⊗_ ε literal
  disjoint-ε-char+ : disjoint ε (char +)
  disjoint-ε-char+ [] (pε , s , (c , pc) , p*) =
    Empty.rec
      (¬cons≡nil (sym (s .snd ∙ cong (_++ s .fst .snd) pc)))
  disjoint-ε-char+ (x ∷ w) (pε , s , _ , p*) =
    Empty.rec (¬cons≡nil pε)

unrolled-string : Grammar ℓ-zero
unrolled-string = ε ⊕ char ⊗ string

unrolled-string' : Grammar ℓ-zero
unrolled-string' = ε ⊕ (string ⊗ char)

unrolled-stringL : Grammar ℓ-zero
unrolled-stringL = ε ⊕ (stringL ⊗ char)

unroll-string≅ : string ≅ unrolled-string
unroll-string≅ = *≅ε⊕A⊗A* char

unroll-string≅' : string ≅ unrolled-string'
unroll-string≅' = *≅ε⊕A*⊗A char

string≅unrolled-stringL : string ≅ unrolled-stringL
string≅unrolled-stringL =
  unroll-string≅'
  ≅∙ ⊕≅ id≅ (⊗≅ string≅stringL id≅)

unroll-stringL≅ : stringL ≅ unrolled-stringL
unroll-stringL≅ = sym≅ string≅stringL ≅∙ string≅unrolled-stringL

unambiguous-unrolled-string : unambiguous unrolled-string
unambiguous-unrolled-string =
    unambiguous≅ unroll-string≅ unambiguous-string

unambiguous-unrolled-string' : unambiguous unrolled-string'
unambiguous-unrolled-string' =
    unambiguous≅ unroll-string≅' unambiguous-string

disjoint-ε-char+' : disjoint ε (char +)
disjoint-ε-char+' = unambig-⊕-is-disjoint unambiguous-unrolled-string

disjoint-ε-char+L : disjoint ε (char +L)
disjoint-ε-char+L = unambig-⊕-is-disjoint unambiguous-unrolled-string'

disjoint-ε-char : disjoint ε char
disjoint-ε-char = disjoint-ε-char+' ∘g id ,&p +-singleton char

disjoint-ε-literal : ∀ c → disjoint ε ＂ c ＂
disjoint-ε-literal c = disjoint-ε-char ∘g id ,&p (literal→char c)

unambiguous-char+ : unambiguous (char +)
unambiguous-char+ = summand-R-is-unambig unambiguous-unrolled-string

unambiguous-char+L : unambiguous (char +L)
unambiguous-char+L = summand-R-is-unambig unambiguous-unrolled-string'

unroll-char+≅ : (char +) ≅ (char ⊕ (char ⊗ char +))
unroll-char+≅ =
  ⊗≅ id≅ unroll-string≅
  ≅∙ char-⊗⊕-distL≅
  ≅∙ ⊕≅ (sym≅ εr≅) id≅

unambiguous-char⊗char+ : unambiguous (char ⊗ char +)
unambiguous-char⊗char+ =
  summand-R-is-unambig (unambiguous≅ unroll-char+≅ unambiguous-char+)

disjoint-char-char⊗char+ : disjoint char (char ⊗ char +)
disjoint-char-char⊗char+ = unambig-⊕-is-disjoint (unambiguous≅ unroll-char+≅ unambiguous-char+)

&string≅ : A ≅ A & string
&string≅ = &⊤≅ ≅∙ &≅ id≅ (sym≅ string≅⊤)

&string-split≅ : A ≅ (A & ε) ⊕ (A & (char +))
&string-split≅ =
  &string≅
  ≅∙ &≅ id≅ unroll-string≅
  ≅∙ &⊕-distL≅

string⊗l-split : A ⊗ string ⊢ A ⊕ (A ⊗ char +)
string⊗l-split =
  (⊗-unit-r ,⊕p id)
  ∘g ⊗⊕-distL
  ∘g id ,⊗ unroll-string≅ .fun

char+⊗l→char+ : char + ⊗ A ⊢ char +
char+⊗l→char+ =
  id ,⊗ string-intro
  ∘g ⊗-assoc⁻

char+L⊗r→char+L : A ⊗ char +L ⊢ char +L
char+L⊗r→char+L =
  string-intro ,⊗ id
  ∘g ⊗-assoc

char+≈char+L : char + ≈ char +L
char+≈char+L =
  disjoint⊕≈
    (≅→≈ id≅)
    disjoint-ε-char+
    disjoint-ε-char+L
    (≅→≈ (sym≅ unroll-string≅ ≅∙ unroll-string≅'))

char+≅char+L : char + ≅ char +L
char+≅char+L = ≈→≅ unambiguous-char+ unambiguous-char+L char+≈char+L

char+⊗r→char+ : A ⊗ char + ⊢ char +
char+⊗r→char+ =
  char+≅char+L .inv
  ∘g char+L⊗r→char+L
  ∘g id ,⊗ char+≅char+L .fun

module _ {c : ⟨ Alphabet ⟩}
  where
  startsWith→char+ : startsWith c ⊢ char +
  startsWith→char+ = literal→char c ,⊗ id

module _ (c c' : ⟨ Alphabet ⟩) where
  same-first :
    ＂ c ＂ & startsWith c' ⊢ ⊕[ x ∈ (c ≡ c') ] ＂ c ＂
  same-first =
    ⊕-elim
      (same-literal c c')
      (⊥-elim
      ∘g disjoint-char-char⊗char+
      ∘g literal→char c ,&p id)
    ∘g &⊕-distL
    ∘g id ,&p
      ((⊗-unit-r ,⊕p (literal→char c' ,⊗ id))
        ∘g ⊗⊕-distL
        ∘g id ,⊗ unroll-string≅ .fun)

unambiguous⌈⌉ : ∀ w → unambiguous ⌈ w ⌉
unambiguous⌈⌉ w = EXTERNAL.isLang→unambiguous (isLang⌈⌉ w)

hasUniqueSplit :
  (A : Grammar ℓA) →
  (B : Grammar ℓB) →
  Type (ℓ-max ℓA ℓB)
hasUniqueSplit A B =
  ∀ (w w' v v' : String) →
    ((A & ⌈ w ⌉) ⊗ (B & ⌈ w' ⌉))
      & ((A & ⌈ v ⌉) ⊗ (B & ⌈ v' ⌉))
    ⊢
    (⊕[ x ∈ w ≡ v ] (A & ⌈ w ⌉) ⊗ (⊕[ x ∈ w' ≡ v' ] B & ⌈ v ⌉))

literal→⌈⌉ : (c : ⟨ Alphabet ⟩) → ＂ c ＂ ⊢ ⌈ [ c ] ⌉
literal→⌈⌉ c = ⊗-unit-r⁻

opaque
  unfolding _&_
  sameString : ∀ w w' → ⌈ w ⌉ & ⌈ w' ⌉ ⊢ ⊕[ x ∈ (w ≡ w') ] (⌈ w ⌉ & ⌈ w' ⌉)
  sameString w w' w'' (p , q) =
    uniquely-supported-⌈⌉ w w'' p
    ∙ sym (uniquely-supported-⌈⌉ w' w'' q) ,
    p , q

isLang⊕⌈⌉ : isLang (⊕[ w ∈ String ] ⌈ w ⌉)
isLang⊕⌈⌉ w x y =
  Σ≡Prop
    (λ w' → isLang⌈⌉ w' w)
    (uniquely-supported-⌈⌉ (x .fst) w (x .snd)
     ∙ sym (uniquely-supported-⌈⌉ (y .fst) w (y .snd)))

unambiguous⊕⌈⌉ : unambiguous (⊕[ w ∈ String ] ⌈ w ⌉)
unambiguous⊕⌈⌉ = EXTERNAL.isLang→unambiguous isLang⊕⌈⌉

whichString≅ : string ≅ ⊕[ w ∈ String ] ⌈ w ⌉
whichString≅ .fun = rec _ the-alg _
  where
  the-alg : Algebra (*Ty char) λ _ → ⊕[ w ∈ String ] ⌈ w ⌉
  the-alg _ = ⊕ᴰ-elim (λ {
      nil → σ [] ∘g lowerG ∘g lowerG
    ; cons →
      ⊕ᴰ-elim (λ w → ⊕ᴰ-elim (λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
      ∘g ⊕ᴰ-distR .fun
      ∘g (lowerG ,⊗ lowerG)
    })
whichString≅ .inv = ⊕ᴰ-elim (λ w → ⌈w⌉→string {w = w})
whichString≅ .sec = unambiguous⊕⌈⌉ _ _
whichString≅ .ret = unambiguous-string _ _

whichString≅' : A ≅ ⊕[ w ∈ String ] (A & ⌈ w ⌉)
whichString≅' =
  &string≅
  ≅∙ &≅ id≅ whichString≅
  ≅∙ &⊕ᴰ-distR≅

++⌈⌉ : ∀ w w' → ⌈ w ⌉ ⊗ ⌈ w' ⌉ ⊢ ⌈ w ++ w' ⌉
++⌈⌉ [] w' = ⊗-unit-l
++⌈⌉ (c ∷ w) w' = id ,⊗ (++⌈⌉ w w') ∘g ⊗-assoc⁻

++⌈⌉⁻ : ∀ w w' →
 ⌈ w ++ w' ⌉
 ⊢
 ⌈ w ⌉ ⊗ ⌈ w' ⌉
++⌈⌉⁻ [] w' = ⊗-unit-l⁻
++⌈⌉⁻ (x ∷ w) w' =
  ⊗-assoc
  ∘g id ,⊗ ++⌈⌉⁻ w w'

++⌈⌉≅ : ∀ w w' → ⌈ w ⌉ ⊗ ⌈ w' ⌉ ≅ ⌈ w ++ w' ⌉
++⌈⌉≅ w w' .fun = ++⌈⌉ w w'
++⌈⌉≅ w w' .inv = ++⌈⌉⁻ w w'
++⌈⌉≅ w w' .sec = unambiguous⌈⌉ (w ++ w') _ _
++⌈⌉≅ [] w' .ret = ⊗-unit-ll⁻
++⌈⌉≅ (x ∷ w) w' .ret =
  the-ret
  where
  opaque
    unfolding ⊗-intro
    the-ret :
      ++⌈⌉≅ (x ∷ w) w' .inv ∘g ++⌈⌉≅ (x ∷ w) w' .fun ≡ id
    the-ret =
      (λ i → ⊗-assoc ∘g id ,⊗ ++⌈⌉≅ w w' .ret i ∘g ⊗-assoc⁻)
      ∙ ⊗-assoc∘⊗-assoc⁻≡id

unambiguous-⌈⌉⊗⌈⌉ : ∀ w w' → unambiguous (⌈ w ⌉ ⊗ ⌈ w' ⌉)
unambiguous-⌈⌉⊗⌈⌉ w w' =
  unambiguous≅ (sym≅ (++⌈⌉≅ w w')) (unambiguous⌈⌉ (w ++ w'))

Split++⌈⌉ :
  ∀ (w x y z u : String) →
  (Split++ w x y z u Sum.⊎ Split++ y z w x u) →
  Grammar ℓ-zero
Split++⌈⌉ w x y z u (Sum.inl the-split) =
  ⌈ w ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ z ⌉
Split++⌈⌉ w x y z u (Sum.inr the-split) =
  ⌈ y ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ x ⌉
