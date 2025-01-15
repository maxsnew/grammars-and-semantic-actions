{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Product Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Dependent.Properties Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Lift.Properties Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet

open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

open StrongEquivalence

opaque
  unfolding literal
  char-length1 : ∀  w → char w → length w ≡ 1
  char-length1 [] (c , p) = Empty.rec (¬nil≡cons p)
  char-length1 (x ∷ []) (c , p) = refl
  char-length1 (x ∷ x₁ ∷ w) (c , p) = Empty.rec (¬cons≡nil (cons-inj₂ p))

module _ (c : ⟨ Alphabet ⟩) where
  opaque
    unfolding literal
    literal→char : ＂ c ＂ ⊢ char
    literal→char = ⊕ᴰ-in c
opaque
  unfolding literal
  isLang-char : isLang char
  isLang-char w (c , p) (c' , p') =
    ΣPathP
      (cons-inj₁ ((sym p) ∙ p') ,
      isProp→PathP (λ i → isLangLiteral _ _) p p')

opaque
  unfolding the-split _⊗_ literal
  unique-splitting-charL :
    (w : String) →
    (p q : (char ⊗ g) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charL {g = g} w (s , (c , p) , q) (s' , (c' , p') , q') =
    ≡-×
      (p ∙ cong (_∷ []) (cons-inj₁ w≡) ∙ sym p')
      (cons-inj₂ w≡)
    where
    w≡ : [ c ] ++ s .fst .snd ≡ [ c' ] ++ s' .fst .snd
    w≡ = sym (s .snd ∙ cong (_++ s. fst .snd) p) ∙ s' .snd ∙ cong (_++ s' .fst .snd) p'

  opaque
    unfolding ⊗-intro
    unique-splitting-literalL :
      {c : ⟨ Alphabet ⟩} →
      (w : String) →
      (p q : (＂ c ＂ ⊗ g) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalL {g = g} {c = c} w p q =
      unique-splitting-charL w ((literal→char c  ,⊗ id) w p ) ((literal→char c ,⊗ id) w q)

  unique-splitting-charR :
    (w : String) →
    (p q : (g ⊗ char) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charR {g = g} w (s , p , (c , q)) (s' , p' , (c' , q')) =
    ≡-×
      (snoc-inj₁ w≡)
      (q ∙ cong (_∷ []) (snoc-inj₂ w≡) ∙ sym q')
    where
    w≡ : s .fst .fst ++ [ c ] ≡ s' .fst .fst ++ [ c' ]
    w≡ = sym (s .snd ∙ cong (s .fst .fst ++_) q) ∙ s' .snd ∙ cong (s' .fst .fst ++_) q'

  opaque
    unfolding ⊗-intro
    unique-splitting-literalR :
      {c : ⟨ Alphabet ⟩} →
      (w : String) →
      (p q : (g ⊗ ＂ c ＂) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalR {g = g} {c = c} w p q =
      unique-splitting-charR w ((id ,⊗ literal→char c) w p ) ((id ,⊗ literal→char c) w q)

module _
  {g : Grammar ℓg}
  (isLang-g : isLang g)
  where
  module _ {c : ⟨ Alphabet ⟩} where
    opaque
      unfolding _⊗_ the-split
      isLang-lit⊗lang : isLang (＂ c ＂ ⊗ g)
      isLang-lit⊗lang w x y =
        Σ≡Prop
          (λ s → isProp× (isLangLiteral c (s .fst .fst)) (isLang-g (s .fst .snd)))
          (Splitting≡ (unique-splitting-literalL w x y))

      isLang-lang⊗lit : isLang (g ⊗ ＂ c ＂)
      isLang-lang⊗lit w x y =
        Σ≡Prop
          (λ s → isProp× (isLang-g (s .fst .fst)) (isLangLiteral c (s .fst .snd)))
          (Splitting≡ (unique-splitting-literalR w x y))
  opaque
    unfolding _⊗_ the-split
    isLang-char⊗lang : isLang (char ⊗ g)
    isLang-char⊗lang w x y =
      Σ≡Prop
        (λ s → isProp× (isLang-char (s .fst .fst)) (isLang-g (s .fst .snd)))
        (Splitting≡ (unique-splitting-charL w x y))

    isLang-lang⊗char : isLang (g ⊗ char)
    isLang-lang⊗char w x y =
      Σ≡Prop
        (λ s → isProp× (isLang-g (s .fst .fst)) (isLang-char (s .fst .snd)))
        (Splitting≡ (unique-splitting-charR w x y))

opaque
  unfolding ⊗-intro
  length-repeat'-char : ∀ n w → (repeat' char n) w → length w ≡ (lower n)
  length-repeat'-char (lift zero) w (roll .w (lift (lift pε))) = ε-length0 w pε
  length-repeat'-char (lift (suc n)) w (roll .w (s , (lift p) , (lift x))) =
    cong length (s .snd)
    ∙ length++ (s .fst .fst) (s .fst .snd)
    ∙ cong₂ _+_ ∣s₁₁∣ ∣s₁₂∣
    where
    ∣s₁₁∣ : length (s .fst .fst) ≡ 1
    ∣s₁₁∣ = char-length1 (s .fst .fst) p

    ∣s₁₂∣ : length (s .fst .snd) ≡ n
    ∣s₁₂∣ = length-repeat'-char (lift n) (s .fst .snd) x


isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉
isLang⌈⌉ [] = isLangε
isLang⌈⌉ (c ∷ w) = isLang-lit⊗lang (isLang⌈⌉ w)

⌈w⌉→string' : ∀ w → ⌈ w ⌉ ⊢ string
⌈w⌉→string' [] = NIL
⌈w⌉→string' (c ∷ w) = CONS ∘g literal→char c ,⊗ ⌈w⌉→string' w

isLang-repeat'-char : ∀ n → isLang (repeat' char n)
isLang-repeat'-char (lift zero) =
  isLang≅
    (LiftG≅2 _ _ _ ≅∙ sym≅ (unroll≅ _ _))
    isLangε
isLang-repeat'-char (lift (suc n)) =
  isLang≅
    (LiftG⊗LiftG≅ _ _ _ _  ≅∙ sym≅ (unroll≅ _ _))
    (isLang-char⊗lang (isLang-repeat'-char (lift n)))

opaque
  unfolding _&_
  disjoint-summands-repeat'-char : disjointSummands⊕ᴰ (repeat' char)
  disjoint-summands-repeat'-char (lift n) (lift m) n≢m w (pn , pm) =
    Empty.rec (n≢m (cong lift (sym (length-repeat'-char (lift n) w pn) ∙ length-repeat'-char (lift m) w pm)))

isLang-repeat-char : isLang (repeat char)
isLang-repeat-char =
  mkIsLang⊕ᴰ
    disjoint-summands-repeat'-char
    isLang-repeat'-char
    (discreteLift discreteℕ)

isLang-string : isLang string
isLang-string =
  isLang≅
    (sym≅ (*continuous char))
    isLang-repeat-char

opaque
  unambiguous-char : unambiguous char
  unambiguous-char = EXTERNAL.isLang→unambiguous isLang-char

  unambiguous-repeat'-char : ∀ n → unambiguous (repeat' char n)
  unambiguous-repeat'-char n = EXTERNAL.isLang→unambiguous (isLang-repeat'-char n)

  unambiguous-repeat-char : unambiguous (repeat char)
  unambiguous-repeat-char = EXTERNAL.isLang→unambiguous isLang-repeat-char

  unambiguous-string : unambiguous string
  unambiguous-string = EXTERNAL.isLang→unambiguous isLang-string

char-⊗⊕-distL⁻ : (char ⊗ g) ⊕ (char ⊗ h) ⊢ char ⊗ (g ⊕ h)
char-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ ⊕-inl) (id ,⊗ ⊕-inr)

char-⊗⊕-distR⁻ : (g ⊗ char) ⊕ (h ⊗ char) ⊢ (g ⊕ h) ⊗ char
char-⊗⊕-distR⁻ = ⊕-elim (⊕-inl ,⊗ id) (⊕-inr ,⊗ id)

char-⊗⊕-distL≅ : char ⊗ (g ⊕ h) ≅ (char ⊗ g) ⊕ (char ⊗ h)
char-⊗⊕-distL≅ .fun = ⊗⊕-distL
char-⊗⊕-distL≅ .inv = char-⊗⊕-distL⁻
char-⊗⊕-distL≅ {g = g} {h = h} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distL≅ {g = g} {h = h} .fun ∘g char-⊗⊕-distL≅ .inv ≡ id
    the-sec i w (inl p) = inl p
    the-sec i w (inr p) = inr p
char-⊗⊕-distL≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_ _⊗_
    the-ret : char-⊗⊕-distL≅ {g = g} {h = h} .inv ∘g char-⊗⊕-distL≅ .fun ≡ id
    the-ret i w (s , p , inl q) = s , p , inl q
    the-ret i w (s , p , inr q) = s , p , inr q

char-⊗⊕-distR≅ : (g ⊕ h) ⊗ char ≅ (g ⊗ char) ⊕ (h ⊗ char)
char-⊗⊕-distR≅ .fun = ⊗⊕-distR
char-⊗⊕-distR≅ .inv = char-⊗⊕-distR⁻
char-⊗⊕-distR≅ {g = g} {h = h} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distR≅ {g = g} {h = h} .fun ∘g char-⊗⊕-distR≅ .inv ≡ id
    the-sec i w (inl p) = inl p
    the-sec i w (inr p) = inr p
char-⊗⊕-distR≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distR _⊕_ _⊗_
    the-ret : char-⊗⊕-distR≅ {g = g} {h = h} .inv ∘g char-⊗⊕-distR≅ .fun ≡ id
    the-ret i w (s , inl p , q) = s , inl p , q
    the-ret i w (s , inr p , q) = s , inr p , q

⊤→string : ⊤ ⊢ string
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤→string' : ⊤ ⊢ string
⊤→string' w _ = mkstring' w

⊤*→string : ∀ {ℓg} → ⊤* {ℓg} ⊢ string
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

string-intro : ∀ {ℓg} {g : Grammar ℓg} → g ⊢ string
string-intro = ⊤→string ∘g ⊤-intro

string≅⊤ : StrongEquivalence string ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = ⊤→string'
string≅⊤ .sec = unambiguous⊤ _ _
string≅⊤ .ret = unambiguous-string _ _

opaque
  unfolding _&_ _⊗_ ε literal
  disjoint-ε-char+ : disjoint ε (char +)
  disjoint-ε-char+ [] (pε , s , (c , pc) , p*) =
    Empty.rec
      (¬cons≡nil (sym (s .snd ∙ cong (_++ s .fst .snd) pc)))
  disjoint-ε-char+ (x ∷ w) (pε , s , pg , p*) =
    Empty.rec (¬cons≡nil pε)

unrolled-string : Grammar ℓ-zero
unrolled-string = ε ⊕ char ⊗ string

unroll-string≅ : string ≅ unrolled-string
unroll-string≅ = *≅ε⊕g⊗g* char

unambiguous-unrolled-string : unambiguous unrolled-string
unambiguous-unrolled-string =
    unambiguous≅ unroll-string≅ unambiguous-string

totallyParseable' : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable' {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') string

disjoint-ε-char+' : disjoint ε (char +)
disjoint-ε-char+' = unambig-⊕-is-disjoint unambiguous-unrolled-string

unambiguous-char+ : unambiguous (char +)
unambiguous-char+ = summand-R-is-unambig unambiguous-unrolled-string

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
