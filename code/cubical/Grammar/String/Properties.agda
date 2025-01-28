{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.List.Properties
open import Cubical.Data.List.More
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.MoreMore
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sum.More
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)

open import Cubical.Relation.Nullary.Base

open import Grammar.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Properties Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Bottom Alphabet
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
open import Grammar.LinearFunction Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
open import Grammar.Inductive.Properties Alphabet

open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

open StrongEquivalence

opaque
  unfolding literal
  char-length1 : ∀ w → char w → length w ≡ 1
  char-length1 [] (c , p) = Empty.rec (¬nil≡cons p)
  char-length1 (x ∷ []) (c , p) = refl
  char-length1 (x ∷ x₁ ∷ w) (c , p) = Empty.rec (¬cons≡nil (cons-inj₂ p))

module _ (c : ⟨ Alphabet ⟩) where
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
    (p : (char ⊗ g) w) →
    (q : (char ⊗ h) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charL  w (s , (c , p) , q) (s' , (c' , p') , q') =
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
      (p : (＂ c ＂ ⊗ g) w) →
      (q : (＂ c ＂ ⊗ h) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalL {g = g} {c = c} w p q =
      unique-splitting-charL w ((literal→char c  ,⊗ id) w p ) ((literal→char c ,⊗ id) w q)

  unique-splitting-charR :
    (w : String) →
    (p : (g ⊗ char) w) →
    (q : (h ⊗ char) w) →
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
      (p : (g ⊗ ＂ c ＂) w) →
      (q : (h ⊗ ＂ c ＂) w) →
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

opaque
  unfolding _⊗_ _&_ the-split literal
  char-⊗&-distL⁻ :
    (char ⊗ g) & (char ⊗ h) ⊢ char ⊗ (g & h)
  char-⊗&-distL⁻ {h = h} w ((s , p , q) , (s' , p' , q')) =
    s , (p , (q , subst h s≡ q'))
    where
    s≡ : s' .fst .snd ≡ s .fst .snd
    s≡ = cons-inj₂
      (cong (_++ s' .fst .snd) (sym (p' .snd))
      ∙ sym (s' .snd)
      ∙ s .snd
      ∙ cong (_++ s .fst .snd) (p .snd)
      )

  char-⊗&-distR⁻ :
    (g ⊗ char) & (h ⊗ char) ⊢ (g & h) ⊗ char
  char-⊗&-distR⁻ {g = g} {h = h} w ((s , p , q) , (s' , p' , q')) =
    s ,
    ((p ,
    subst h
      (cong (λ z → z .fst)
      (sym (unique-splitting-charR {g = g} {h = h}
        w (s , p , q) (s' , p' , q')))) p') , q)

char-⊗&-distR≅ : (g & h) ⊗ char ≅ (g ⊗ char) & (h ⊗ char)
char-⊗&-distR≅ .fun = ⊗&-distR
char-⊗&-distR≅ .inv = char-⊗&-distR⁻
char-⊗&-distR≅ {g = g} {h = h} .sec = the-sec
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR
    the-sec : char-⊗&-distR≅ {g = g} {h = h} .fun ∘g char-⊗&-distR≅ .inv ≡ id
    the-sec = funExt λ w → funExt λ p →
      ΣPathP (refl ,
        ΣPathP (
          (Splitting≡ (unique-splitting-charR w (p .fst) (p .snd))) ,
          ΣPathP (
            symP (transport-filler _ (fst (p .snd .snd))) ,
            isProp→PathP (λ i → isLang-char _) _ _
          )
        )
      )

char-⊗&-distR≅ .ret = the-ret
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR
    the-ret : char-⊗&-distR≅ {g = g} {h = h} .inv ∘g char-⊗&-distR≅ .fun ≡ id
    the-ret {h = h} = funExt λ w → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          (ΣPathP (
            refl ,
            symP (transport-filler _ (p .snd .fst .snd)
            ∙ cong (λ z → transport (λ i → h (z i)) (p .snd .fst .snd))
              (isSetString _ _ _ _))
          )) ,
          refl
        ))
      )

⊤→string : ⊤ ⊢ string
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤→string' : ⊤ ⊢ string
⊤→string' w _ = mkstring' w

⊤*→string : ∀ {ℓg} → ⊤* {ℓg} ⊢ string
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

string≅stringL : string ≅ stringL
string≅stringL = *≅*L char

string-intro : ∀ {ℓg} {g : Grammar ℓg} → g ⊢ string
string-intro = ⊤→string ∘g ⊤-intro

stringL-intro : ∀ {ℓg} {g : Grammar ℓg} → g ⊢ stringL
stringL-intro = string≅stringL .fun ∘g string-intro

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

unrolled-string' : Grammar ℓ-zero
unrolled-string' = ε ⊕ (string ⊗ char)

unrolled-stringL : Grammar ℓ-zero
unrolled-stringL = ε ⊕ (stringL ⊗ char)

unroll-string≅ : string ≅ unrolled-string
unroll-string≅ = *≅ε⊕g⊗g* char

unroll-string≅' : string ≅ unrolled-string'
unroll-string≅' = *≅ε⊕g*⊗g char

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

totallyParseable' : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable' {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') string

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

&string≅ : g ≅ g & string
&string≅ = &⊤≅ ≅∙ &≅ id≅ (sym≅ string≅⊤)

&string-split≅ : g ≅ (g & ε) ⊕ (g & (char +))
&string-split≅ =
  &string≅
  ≅∙ &≅ id≅ unroll-string≅
  ≅∙ &⊕-distL≅

string⊗l-split : g ⊗ string ⊢ g ⊕ (g ⊗ char +)
string⊗l-split =
  (⊗-unit-r ,⊕p id)
  ∘g ⊗⊕-distL
  ∘g id ,⊗ unroll-string≅ .fun

char+⊗l→char+ : char + ⊗ g ⊢ char +
char+⊗l→char+ =
  id ,⊗ string-intro
  ∘g ⊗-assoc⁻

char+L⊗r→char+L : g ⊗ char +L ⊢ char +L
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

char+⊗r→char+ : g ⊗ char + ⊢ char +
char+⊗r→char+ =
  char+≅char+L .inv
  ∘g char+L⊗r→char+L
  ∘g id ,⊗ char+≅char+L .fun

module _ (c c' : ⟨ Alphabet ⟩) where
  same-first :
    ＂ c ＂ & (＂ c' ＂ ⊗ string) ⊢ ⊕[ x ∈ (c ≡ c') ] ＂ c ＂
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

  -- There's almost surely a way to do this in the logic
  -- but I am just going to axiomatize it
  opaque
    unfolding literal _⊗_ _&_
    same-first' :
      (＂ c ＂ ⊗ string) & (＂ c' ＂ ⊗ string) ⊢
        ⊕[ x ∈ (c ≡ c') ] (＂ c ＂ ⊗ string)
    same-first' w ((s , pc , str) , (s' , pc' , str')) =
      c≡c' , s , (pc , str)
      where
      c≡c' : c ≡ c'
      c≡c' =
        cons-inj₁
        (cong (_++ s .fst .snd) (sym pc)
        ∙ (sym (s .snd)
        ∙ (s' .snd))
        ∙ cong (_++ s' .fst .snd) pc')

firstChar≅ : g ≅ (g & ε) ⊕ ⊕[ c ∈ ⟨ Alphabet ⟩ ] (g & (＂ c ＂ ⊗ string))
firstChar≅ =
  &string-split≅
  ≅∙ ⊕≅ id≅ (&≅ id≅ ⊕ᴰ-distL ≅∙ &⊕ᴰ-distR≅)

unambiguous⌈⌉ : ∀ w → unambiguous ⌈ w ⌉
unambiguous⌈⌉ w = EXTERNAL.isLang→unambiguous (isLang⌈⌉ w)

hasUniqueSplit :
  (g : Grammar ℓg) →
  (h : Grammar ℓh) →
  Type (ℓ-max ℓg ℓh)
hasUniqueSplit g h = 
  ∀ (w w' v v' : String) →
    ((g & ⌈ w ⌉) ⊗ (h & ⌈ w' ⌉))
      & ((g & ⌈ v ⌉) ⊗ (h & ⌈ v' ⌉))
    ⊢
    (⊕[ x ∈ w ≡ v ] (g & ⌈ w ⌉) ⊗ (⊕[ x ∈ w' ≡ v' ] h & ⌈ v ⌉))

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
      nil → ⊕ᴰ-in [] ∘g lowerG ∘g lowerG
    ; cons →
      ⊕ᴰ-elim (λ w → ⊕ᴰ-elim (λ c → ⊕ᴰ-in (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
      ∘g ⊕ᴰ-distR .fun
      ∘g (lowerG ,⊗ lowerG)
    })
whichString≅ .inv = ⊕ᴰ-elim (λ w → ⌈w⌉→string {w = w})
whichString≅ .sec = unambiguous⊕⌈⌉ _ _
whichString≅ .ret = unambiguous-string _ _

whichString≅' : g ≅ ⊕[ w ∈ String ] (g & ⌈ w ⌉)
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
  (Split++ w x y z u ⊎ Split++ y z w x u) →
  Grammar ℓ-zero
Split++⌈⌉ w x y z u (inl the-split) =
  ⌈ w ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ z ⌉
Split++⌈⌉ w x y z u (inr the-split) =
  ⌈ y ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ x ⌉

-- module _
--   (g : Grammar ℓg)
--   (h : Grammar ℓh)
--   (k : Grammar ℓk)
--   (l : Grammar ℓl)
--   where
--   opaque
--     unfolding ⊗-intro _&_ _⊕_ ⊕-elim
--     Split⊗' :
--       (
--       ⊕[ w ∈ String ]
--       ⊕[ x ∈ String ]
--       ⊕[ y ∈ String ]
--       ⊕[ z ∈ String ]
--         (
--         ((g & ⌈ w ⌉) ⊗ (h & ⌈ x ⌉)) &
--         ((k & ⌈ y ⌉) ⊗ (l & ⌈ z ⌉))
--         )
--       )
--       ≅
--       (
--       ⊕[ w ∈ String ]
--       ⊕[ x ∈ String ]
--         ((g & k & ⌈ w ⌉) ⊗ (h & l & ⌈ x ⌉))
--       )
--       ⊕
--       (
--       ⊕[ w ∈ String ]
--       ⊕[ x ∈ String ]
--       ⊕[ y ∈ String ]
--       ⊕[ z ∈ String ]
--       ⊕[ v ∈ NonEmptyString ]
--         (
--         (((g & ⌈ w ⌉) & ((k & ⌈ y ⌉) ⊗ ⌈ v .fst ⌉)) ⊗ (h & ⌈ x ⌉)) &
--         ((k & ⌈ y ⌉) ⊗ ((l & ⌈ z ⌉) & (⌈ v .fst ⌉ ⊗ (h & ⌈ x ⌉))))
--         )
--       )
--       ⊕
--       (
--       ⊕[ w ∈ String ]
--       ⊕[ x ∈ String ]
--       ⊕[ y ∈ String ]
--       ⊕[ z ∈ String ]
--       ⊕[ v ∈ NonEmptyString ]
--         (
--         (((k & ⌈ y ⌉) & ((g & ⌈ w ⌉) ⊗ ⌈ v .fst ⌉)) ⊗ (l & ⌈ z ⌉)) &
--         ((g & ⌈ w ⌉) ⊗ ((h & ⌈ x ⌉) & (⌈ v .fst ⌉ ⊗ (l & ⌈ z ⌉))))
--         )
--       )
--     Split⊗' .fun the-str
--       (w , x , y , z , (s , pg , ph) , (s' , pk , pl)) =
--       Sum.rec
--         (λ (s₁≡ , s₂≡) →
--           inl (
--             w ,
--             x ,
--             s ,
--             (pg .fst ,
--               (
--                subst k (sym s₁≡) (pk .fst) ,
--                pg .snd
--               )) ,
--             (ph .fst ,
--               (
--               subst l (sym s₂≡) (pl .fst) ,
--               ph .snd
--             ))
--           )
--         )
--         (Sum.rec
--           (λ {
--             (([] , notmt) , _) →
--              Empty.rec (notmt refl)
--           ; ((c ∷ v , notmt) , the-split) →
--              inr (inr (
--                w ,
--                x ,
--                y ,
--                z ,
--                (c ∷ v , notmt) ,
--                (s' ,
--                  ((pk ,
--                  ((_ , sym (the-split .fst)) , (pg , (internalize (c ∷ v))))) ,
--                  pl)) ,
--                (s ,
--                  (pg ,
--                  (ph , ((_ , the-split .snd) , ((internalize (c ∷ v)) ,
--                  pl)))))
--               ))
--           })
--           (λ {
--             (([] , notmt) , _) →
--              Empty.rec (notmt refl)
--           ; ((c ∷ v , notmt) , the-split) →
--              inr (inl (
--                w ,
--                x ,
--                y ,
--                z ,
--                (c ∷ v , notmt) ,
--                (s ,
--                  ((pg ,
--                  ((_ , sym (the-split .fst)) , (pk , (internalize (c ∷ v))))) ,
--                  ph)) ,
--                (s' , pk , (pl , ((_ , the-split .snd) , ((internalize (c ∷ v)) , ph))))
--               ))
--           })
--         )
--         (splittingTrichotomy' the-str s s')
--     Split⊗' .inv the-str (inl (w , x , p)) =
--       w ,
--       x ,
--       w ,
--       x ,
--       ((p .fst) ,
--         (((p .snd .fst .fst) , (p .snd .fst .snd .snd)) ,
--         ((p .snd .snd .fst) , (p .snd .snd .snd .snd)))) ,
--       (p .fst ,
--         ((p .snd .fst .snd .fst) , (p .snd .fst .snd .snd)) ,
--         ((p .snd .snd .snd .fst) , (p .snd .snd .snd .snd)))
--       -- ((_ , the-str≡w++x) ,
--       --   (subst g (sym w≡) (p .snd .fst .fst) , internalize w) ,
--       --   (subst h (sym x≡) (p .snd .snd .fst) , internalize x)) ,
--       -- ((_ , the-str≡w++x) ,
--       --   ((subst k (sym w≡) (p .snd .fst .snd .fst)) , (internalize w)) ,
--       --   ((subst l (sym x≡) (p .snd .snd .snd .fst)) , (internalize x))
--       -- )
--       -- where
--       -- w≡ : w ≡ p .fst .fst .fst
--       -- w≡ =
--       --   uniquely-supported-⌈⌉
--       --   w (p .fst .fst .fst)
--       --   (p .snd .fst .snd .snd)

--       -- x≡ : x ≡ p .fst .fst .snd
--       -- x≡ =
--       --   uniquely-supported-⌈⌉
--       --   x (p .fst .fst .snd)
--       --   (p .snd .snd .snd .snd)

--       -- the-str≡w++x : the-str ≡ w ++ x
--       -- the-str≡w++x =
--       --   sym
--       --   (
--       --   uniquely-supported-⌈⌉ (w ++ x) the-str
--       --   ((++⌈⌉ w x ∘g ((&-π₂ ∘g &-π₂) ,⊗ (&-π₂ ∘g &-π₂))) the-str p)
--       --   )

--     Split⊗' .inv the-str (inr (inl (w , x , y , z , ([] , notmt) , p))) =
--       Empty.rec (notmt refl)
--     Split⊗' .inv the-str (inr (inl (w , x , y , z , (c ∷ v , notmt) , p))) =
--       w ,
--       x ,
--       y ,
--       z ,
--       (p .fst .fst ,
--         ((p .fst .snd .fst .fst .fst ,
--         p .fst .snd .fst .fst .snd) ,
--         (p .fst .snd .snd .fst ,
--         p .fst .snd .snd .snd))) ,
--       (p .snd .fst ,
--         ((p .snd .snd .fst .fst) ,
--         (p .snd .snd .fst .snd)) ,
--         ((p .snd .snd .snd .fst .fst) ,
--         (p .snd .snd .snd .fst .snd)))
--       -- ((_ , {!!}) , ((p .fst .snd .fst .fst) , (p .fst .snd .snd))) ,
--       -- ((_ , {!!}) , (p .snd .snd .fst) , (p .snd .snd .snd .fst))
--       -- where
--       -- w≡ : w ≡ {!!}
--       -- w≡ =
--       --   {!!}
--       --   -- uniquely-supported-⌈⌉
--       --   -- w (p .fst .fst .fst)
--       --   -- (p .snd .fst .snd .snd)

--       -- x≡ : x ≡ {!!}
--       -- x≡ =
--       --   {!!}
--       --   -- uniquely-supported-⌈⌉
--       --   -- x (p .fst .fst .snd)
--       --   -- (p .snd .snd .snd .snd)
--       -- y≡ : y ≡ {!!}
--       -- y≡ =
--       --   {!!}

--       -- z≡ : z ≡ {!!}
--       -- z≡ =
--       --   {!!}

--       -- the-str≡w++x : the-str ≡ w ++ x
--       -- the-str≡w++x =
--       --   {!!}
--       --   -- sym
--       --   -- (
--       --   -- uniquely-supported-⌈⌉ (w ++ x) the-str
--       --   -- ((++⌈⌉ w x ∘g ((&-π₂ ∘g &-π₂) ,⊗ (&-π₂ ∘g &-π₂))) the-str p)
--       --   -- )

--       -- the-str≡y++z : the-str ≡ y ++ z
--       -- the-str≡y++z =
--       --   {!!}

--     Split⊗' .inv the-str (inr (inr (w , x , y , z , ([] , notmt) , p))) =
--       Empty.rec (notmt refl)
--     Split⊗' .inv the-str (inr (inr (w , x , y , z , (c ∷ v , notmt) , p))) =
--       w ,
--       x ,
--       y ,
--       z ,
--       (p .snd .fst ,
--         ((p .snd .snd .fst .fst) ,
--         (p .snd .snd .fst .snd)) ,
--         ((p .snd .snd .snd .fst .fst) ,
--         (p .snd .snd .snd .fst .snd))) ,
--       (p .fst .fst ,
--         ((p .fst .snd .fst .fst .fst ,
--         p .fst .snd .fst .fst .snd) ,
--         (p .fst .snd .snd .fst ,
--         p .fst .snd .snd .snd)))
--     Split⊗' .sec =
--       -- ⊕≡ _ _
--       --   (⊕ᴰ≡ _ _ (λ w → ⊕ᴰ≡ _ _ λ x →
--       --     Sum.elim
--       --       {C = {!!}}
--       --       {!!}
--       --       {!!}
--       --       {!Split⊗' .inv ∘g ⊕-inl ∘g ⊕ᴰ-in w ∘g ⊕ᴰ-in w!}
--       --   ))
--       --   {!!}
--       funExt λ the-str → funExt λ {
--         (inl (w , x , p)) →
--           {!!}
--       ; (inr (inl (w , x , y , z , ([] , notmt) , p))) →
--         Empty.rec (notmt refl)
--       ; (inr (inl (w , x , y , z , (c ∷ v , notmt) , p))) → {!!}
--       ; (inr (inr (w , x , y , z , ([] , notmt) , p))) →
--         Empty.rec (notmt refl)
--       ; (inr (inr (w , x , y , z , (c ∷ v , notmt) , p))) → {!!}
--       }
--     Split⊗' .ret = {!!}

-- open LogicalEquivalence
-- split++⌈⌉≈ :
--   ∀ (w x y z : String) →
--   (⌈ w ⌉ ⊗ ⌈ x ⌉) & (⌈ y ⌉ ⊗ ⌈ z ⌉)
--     ≈
--   ⊕[ v ∈ (Σ[ u ∈ String ] (Split++ w x y z u ⊎ Split++ y z w x u)) ]
--     Split++⌈⌉ w x y z (v .fst) (v .snd)
-- split++⌈⌉≈ w x y z .fun =
--   ⊕ᴰ-elim (λ string≡ →
--     let (liason , split++pf) = split++ w x y z string≡ in
--     Sum.rec
--       (λ the-Split++ →
--         ⊕ᴰ-in (liason , inl the-Split++)
--         ∘g id ,⊗ (++⌈⌉⁻ liason z)
--         ∘g ++⌈⌉⁻ w _
--         ∘g transportG (cong (λ u → ⌈ w ++ u ⌉) (the-Split++ .snd))
--         ∘g &-π₁
--       )
--       (λ the-Split++ →
--         ⊕ᴰ-in (liason , inr the-Split++)
--         ∘g id ,⊗ (++⌈⌉⁻ liason x)
--         ∘g ++⌈⌉⁻ y _
--         ∘g transportG (cong (λ u → ⌈ y ++ u ⌉) (the-Split++ .snd))
--         ∘g &-π₂
--       )
--       split++pf
--   )
--   ∘g sameString (w ++ x) (y ++ z)
--   ∘g ++⌈⌉ w x ,&p ++⌈⌉ y z
-- split++⌈⌉≈ w x y z .inv =
--   ⊕ᴰ-elim λ {
--     (liason , inl split≡) →
--       (id ,⊗ (transportG (cong ⌈_⌉ (sym (split≡ .snd))) ∘g ++⌈⌉ liason z))
--         ,&p ((transportG (cong ⌈_⌉ (split≡ .fst)) ∘g ++⌈⌉ w liason) ,⊗ id ∘g ⊗-assoc)
--       ∘g &-Δ
--   ; (liason , inr split≡) →
--       ((transportG (cong ⌈_⌉ (split≡ .fst)) ∘g ++⌈⌉ y liason) ,⊗ id ∘g ⊗-assoc)
--         ,&p id ,⊗ (transportG (cong ⌈_⌉ (sym (split≡ .snd))) ∘g ++⌈⌉ liason x)
--       ∘g &-Δ
--   }
-- -- Can be upgraded to a strong equivalence if w and y are different lengths
-- -- split++⌈⌉≅ w x y z .sec =
-- --   mkUnambiguous⊕ᴰ
-- --     (λ {
-- --       (v , inl s) (v' , inl s') v≢v' →
-- --         let
-- --           vs≡v's' : (v , s) ≡ (v' , s')
-- --           vs≡v's' = isPropΣSplit++ (Alphabet .snd) _ _ _ _ _ _
-- --           in
-- --         Empty.rec (v≢v' λ i → (vs≡v's' i .fst , inl (vs≡v's' i .snd)))
-- --     ; (v , inr s) (v' , inl s') v≢v' →
-- --         Empty.rec (v≢v'
-- --           {!!}
-- --         )
-- --     ; (v , inl s) (v' , inr s') v≢v' →
-- --         Empty.rec {!!}
-- --     ; (v , inr s) (v' , inr s') v≢v' →
-- --         let
-- --           vs≡v's' : (v , s) ≡ (v' , s')
-- --           vs≡v's' = isPropΣSplit++ (Alphabet .snd) _ _ _ _ _ _
-- --           in
-- --         Empty.rec (v≢v' λ i → (vs≡v's' i .fst , inr (vs≡v's' i .snd)))
-- --     }
-- --     )
-- --     {!!}
-- --     (discreteΣ discString λ u →
-- --       discrete⊎
-- --         (discreteΣ (λ _ _ → yes (isSetString (w ++ u) y _ _)) (λ _ → λ _ _ → yes (isSetString x (u ++ z) _ _)))
-- --         (discreteΣ (λ _ _ → yes (isSetString (y ++ u) w _ _)) (λ _ → λ _ _ → yes (isSetString z (u ++ x) _ _)))
-- --         )
-- --     _
-- --     id
-- -- split++⌈⌉≅ w x y z .ret = &unambiguous (unambiguous-⌈⌉⊗⌈⌉ w x) (unambiguous-⌈⌉⊗⌈⌉ y z) _ _


-- {--
-- -- Building some axioms for splitting a ⊗ across a &
-- --
-- -- That is, the grammar (g ⊗ h) & (k ⊗ l)
-- -- should break into a trichotomy that reasons if
-- -- the splitting is the same across the tensors,
-- -- if the first splitting forms a prefix of the second,
-- -- of symmetrically if the second forms a prefix of the first
-- --
-- --
-- --   |    g     |         h          |
-- -- w ---------------------------------
-- --   |    k     |         l          |
-- --
-- --
-- --   |    g     |         h          |
-- -- w ---------------------------------
-- --   |  k  |           l             |
-- --
-- --
-- --   |  g  |           h             |
-- -- w ---------------------------------
-- --   |    k     |         l          |
-- --
-- --}
module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (l : Grammar ℓl)
  where

  sameSplittingG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  sameSplittingG = (g & k) ⊗ (h & l)

  firstPrefixG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  firstPrefixG =
    ⊕[ w ∈ String ]
    ⊕[ x ∈ String ]
    ⊕[ y ∈ String ]
    ⊕[ z ∈ String ]
    ⊕[ v ∈ NonEmptyString ]
      (
      ((g & ⌈ w ⌉) & (⌈ y ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (h & ⌈ x ⌉))
      &
      ((k & ⌈ y ⌉) ⊗ ((l & ⌈ z ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ x ⌉)))
      )

  secondPrefixG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  secondPrefixG =
    ⊕[ w ∈ String ]
    ⊕[ x ∈ String ]
    ⊕[ y ∈ String ]
    ⊕[ z ∈ String ]
    ⊕[ v ∈ NonEmptyString ]
      (
      ((k & ⌈ y ⌉) & (⌈ w ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (l & ⌈ z ⌉))
      &
      ((g & ⌈ w ⌉) ⊗ ((h & ⌈ x ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ z ⌉)))
      )

  module _ (w : String) (s s' : Splitting w) where
    splittingTrichotomyG : splittingTrichotomyTy' w s s' → Type _
    splittingTrichotomyG (inl x) =
      (g & k) (s .fst .fst) × (h & l) (s .fst .snd)
    splittingTrichotomyG (inr (inl (([] , notmt) , x))) = Empty.⊥*
    splittingTrichotomyG (inr (inl ((c ∷ v , notmt) , x))) =
      g (s .fst .fst) ×
      h (s .fst .snd) ×
      k (s' .fst .fst) ×
      l (s' .fst .snd) ×
      (s .fst .fst ++ c ∷ v ≡ s' .fst .fst) ×
      (s .fst .snd ≡ c ∷ v ++ s' .fst .snd)
    splittingTrichotomyG (inr (inr (([] , notmt) , x))) = Empty.⊥*
    splittingTrichotomyG (inr (inr ((c ∷ v , notmt) , x))) =
      g (s .fst .fst) ×
      h (s .fst .snd) ×
      k (s' .fst .fst) ×
      l (s' .fst .snd) ×
      (s' .fst .fst ++ c ∷ v ≡ s .fst .fst ) ×
      (s' .fst .snd ≡ c ∷ v ++ s . fst .snd)

    open Iso
    opaque
      unfolding ⊗-intro _&_ has-split
      parseIso :
        ∀ (st : splittingTrichotomyTy' w s s') →
        Iso
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd))
          (splittingTrichotomyG st)
      parseIso (inl x) .fun y =
        (y .fst  , subst k (sym (x .fst)) (y .snd .snd .fst)) ,
        (y .snd .fst , subst l (sym (x .snd)) (y .snd .snd .snd))
      parseIso (inl x) .inv y =
        (y .fst .fst) , ((y .snd .fst) ,
        ((subst k (x .fst) (y .fst .snd)) ,
        (subst l (x .snd) (y .snd .snd))))
      parseIso (inl x) .rightInv y =
        ≡-× (≡-× refl (subst⁻Subst k (x .fst) (y .fst .snd)))
            (≡-× refl (subst⁻Subst l (x .snd) (y .snd .snd)))
      parseIso (inl x) .leftInv y =
        ≡-× refl (≡-× refl
          (≡-×
            (substSubst⁻ k (x .fst) (y .snd .snd .fst))
            (substSubst⁻ l (x .snd) (y .snd .snd .snd))))
      parseIso (inr (inl (([] , notmt) , st))) =
        Empty.rec (notmt refl)
      parseIso (inr (inl ((c ∷ v , _) , st))) .fun y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd ,
        st .fst ,
        st .snd
      parseIso (inr (inl ((c ∷ v , _) , st))) .inv y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst
      parseIso (inr (inl ((c ∷ v , _) , st))) .rightInv y i =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst ,
        isSetString _ _ (st .fst) (y .snd .snd .snd .snd .fst) i ,
        isSetString _ _ (st .snd) (y .snd .snd .snd .snd .snd) i
      parseIso (inr (inl ((c ∷ v , _) , st))) .leftInv y = refl
      parseIso (inr (inr (([] , notmt) , st))) =
        Empty.rec (notmt refl)
      parseIso (inr (inr ((c ∷ v , _) , st))) .fun y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd ,
        st .fst ,
        st .snd
      parseIso (inr (inr ((c ∷ v , _) , st))) .inv y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst
      parseIso (inr (inr ((c ∷ v , _) , st))) .rightInv y i =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst ,
        isSetString _ _ (st .fst) (y .snd .snd .snd .snd .fst) i ,
        isSetString _ _ (st .snd) (y .snd .snd .snd .snd .snd) i
      parseIso (inr (inr ((c ∷ v , _) , st))) .leftInv y = refl

  open Iso
  opaque
    unfolding parseIso ⊗-intro _&_ mk&⌈⌉
    asdf :
      (w : String) →
      Iso
        (((g ⊗ h) & (k ⊗ l)) w)
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd)))
    asdf w .fun p =
      p .fst .fst , p .snd .fst ,
      p .fst .snd .fst ,
      p .fst .snd .snd ,
      p .snd .snd .fst ,
      p .snd .snd .snd
    asdf w .inv (s , s' , p) =
      (s , (p .fst) , (p .snd .fst)) ,
      (s' , (p .snd .snd .fst) , (p .snd .snd .snd))
    asdf w .rightInv _ = refl
    asdf w .leftInv _ = refl

    wert :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd)))
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
           splittingTrichotomyG w s s' (splittingTrichotomy' w s s')
         )
    wert w .fun (s , s' , p) =
      s , (s' , parseIso w s s' (splittingTrichotomy' w s s') .fun p)
    wert w .inv (s , s' , p) =
     s , (s' , (parseIso w s s' (splittingTrichotomy' w s s') .inv p))
    wert w .rightInv (s , s' , p) =
      ΣPathP (refl , (ΣPathP (refl ,
        parseIso w s s' (splittingTrichotomy' w s s') .rightInv p
      )))
    wert w .leftInv (s , s' , p) =
      ΣPathP (refl , (ΣPathP (refl ,
        parseIso w s s' (splittingTrichotomy' w s s') .leftInv p
      )))

    splittingTrichotomyG-inl≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ sameSplitting w s s' ]
           splittingTrichotomyG w s s' (inl x)
         )
        (sameSplittingG w)
    splittingTrichotomyG-inl≅ w .fun (s , s' , x , p) =
      s , ((p .fst) , (p .snd))
    splittingTrichotomyG-inl≅ w .inv (s , pgk , phl) =
      s , s , (refl , refl) , pgk , phl
    splittingTrichotomyG-inl≅ w .rightInv (s , pgk , phl) = refl
    splittingTrichotomyG-inl≅ w .leftInv (s , s' , x , p) =
      ΣPathP (refl , (ΣPathP ((Splitting≡ (≡-× (x .fst) (x .snd))) ,
        (ΣPathP ((ΣPathP (
          isProp→PathP (λ _ → isSetString _ _) refl (x .fst) ,
          isProp→PathP (λ _ → isSetString _ _) refl (x .snd)
          )) ,
          refl)))))

    splittingTrichotomyG-inr-inl≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ splittingPrefix w s' s ]
           splittingTrichotomyG w s s' (inr (inl x))
         )
        (secondPrefixG w)
    splittingTrichotomyG-inr-inl≅ ww .fun
      (s' , s , ((c ∷ v , notmt) , split++) , p) =
        s' .fst .fst , s' .fst .snd ,
        s .fst .fst , s .fst .snd ,
        ((c ∷ v , notmt)) ,
        (s , ((mk&⌈⌉ k (p .snd .snd .fst) ,
          (_ , (sym (split++ .fst))) , ((mk⌈⌉ (s' .fst .fst)) , (mk⌈⌉ (c ∷ v)))) ,
          mk&⌈⌉ l (p .snd .snd .snd .fst))) ,
        s' , ((mk&⌈⌉ g(p .fst)) ,
          ((mk&⌈⌉ h (p .snd .fst)) ,
          ((_ , split++ .snd) , ((mk⌈⌉ (c ∷ v)) , (mk⌈⌉ (s .fst .snd))))))
    splittingTrichotomyG-inr-inl≅ ww .inv
      (w , x , y , z , ([] , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))
      ) =
      Empty.rec (notmt refl)
    splittingTrichotomyG-inr-inl≅ ww .inv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s' , (pk , (t , pw , pv)) , pl) ,
      (s , pg , (ph , (t' , pv' , pz)))
      ) =
      s , s' ,
      ((c ∷ v , notmt) ,
        s'11≡ ,
        s12≡) ,
      pg .fst ,
      ph .fst ,
      pk .fst ,
      pl .fst ,
      s'11≡ ,
      s12≡
      where
      s11≡t11 : s .fst .fst ≡ t .fst .fst
      s11≡t11 =
        sym (⌈⌉→≡ w (s .fst .fst) (pg .snd))
        ∙ (⌈⌉→≡ w (t .fst .fst) pw)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s'11≡ : s .fst .fst ++ c ∷ v ≡ s' .fst .fst
      s'11≡ = cong₂ _++_ s11≡t11 cv≡t12 ∙ sym (t .snd)

      s12≡ : s .fst .snd ≡ c ∷ v ++ s' .fst .snd
      s12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ z (t' .fst .snd) pz)
            ∙ (⌈⌉→≡ z (s' .fst .snd) (pl .snd)))
    splittingTrichotomyG-inr-inl≅ ww .rightInv
      (w , x , y , z , ([] , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      Empty.rec (notmt refl)
    splittingTrichotomyG-inr-inl≅ ww .rightInv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      ΣPathP5 (
        sym (⌈⌉→≡ _ _ (pg .snd)) ,
        sym (⌈⌉→≡ _ _ (ph .snd)) ,
        sym (⌈⌉→≡ _ _ (pk .snd)) ,
        sym (⌈⌉→≡ _ _ (pl .snd)) ,
        refl ,
        ΣPathP5 (
          ΣPathP2 (
            refl ,
            ΣPathP3 (
              ΣPathPProp (λ _ → isLang⌈⌉ y (s .fst .fst)) refl ,
              Splitting≡
                (≡-×
                  (sym (⌈⌉→≡ w (s' .fst .fst) (pg .snd)) ∙ ⌈⌉→≡ w (t .fst .fst) pw)
                  (⌈⌉→≡ _ _ pv)
                ) ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i) )
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i₁)) ∙
                      ⌈⌉→≡ w (t .fst .fst) pw)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .fst)
                  )
                (mk⌈⌉ (s' .fst .fst))
                pw ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i₁)) ∙
                      ⌈⌉→≡ w (t .fst .fst) pw)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .snd)
                  )
                (mk⌈⌉ (c ∷ v))
                pv
              ) ,
            ΣPathPProp (λ _ → isLang⌈⌉ z (s .fst .snd)) refl
            ) ,
          refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ w (s' .fst .fst)) refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ x (s' .fst .snd)) refl ,
          Splitting≡
            (≡-×
              (⌈⌉→≡ _ _ pv')
              (sym (⌈⌉→≡ z _ (pl .snd)) ∙ ⌈⌉→≡ z _ pz)
            ) ,
          ΣPathP (
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i₁)) ∙
                     ⌈⌉→≡ z (t' .fst .snd) pz))
                   i .fst .fst)
                )
                (mk⌈⌉ (c ∷ v))
                pv' ,
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i))
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i₁)) ∙
                     ⌈⌉→≡ z (t' .fst .snd) pz))
                   i .fst .snd)
                )
                (mk⌈⌉ (s .fst .snd))
                pz
            
          ))
        )
      where
      s'11≡t11 : s' .fst .fst ≡ t .fst .fst
      s'11≡t11 =
        sym (⌈⌉→≡ w (s' .fst .fst) (pg .snd))
        ∙ (⌈⌉→≡ w (t .fst .fst) pw)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s11≡ : s' .fst .fst ++ c ∷ v ≡ s .fst .fst
      s11≡ = cong₂ _++_ s'11≡t11 cv≡t12 ∙ sym (t .snd)

      s'12≡ : s' .fst .snd ≡ c ∷ v ++ s .fst .snd
      s'12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ z (t' .fst .snd) pz)
            ∙ (⌈⌉→≡ z (s .fst .snd) (pl .snd)))
    splittingTrichotomyG-inr-inl≅ ww .leftInv
      (s , s' , ((c ∷ v , notmt) , split++) , p) =
      ΣPathP3 (
        refl ,
        refl ,
        ΣPathP2 (
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        ) ,
        ΣPathP5 (
          refl ,
          refl ,
          refl ,
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        )
      )

    splittingTrichotomyG-inr-inr≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ splittingPrefix w s s' ]
           splittingTrichotomyG w s s' (inr (inr x))
         )
        (firstPrefixG w)
    splittingTrichotomyG-inr-inr≅ ww .fun
      (s' , s , ((c ∷ v , notmt) , split++) , p) =
      s' .fst .fst , s' .fst .snd ,
      s .fst .fst , s .fst .snd ,
      ((c ∷ v , notmt)) ,
      (s' , ((mk&⌈⌉ g (p .fst) ,
        (_ , (sym (split++ .fst))) , ((mk⌈⌉ (s .fst .fst)) , (mk⌈⌉ (c ∷ v)))) ,
        mk&⌈⌉ h (p .snd .fst))) ,
      (s , ((mk&⌈⌉ k (p .snd .snd .fst)) ,
        ((mk&⌈⌉ l (p .snd .snd .snd .fst)) ,
        ((_ , split++ .snd) , ((mk⌈⌉ (c ∷ v)) , (mk⌈⌉ (s' .fst .snd)))))))
    splittingTrichotomyG-inr-inr≅ ww .inv
      (w , x , y , z , ([] , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))
      ) =
      Empty.rec (notmt refl)
    splittingTrichotomyG-inr-inr≅ ww .inv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s' , (pg , (t , py , pv)) , ph) ,
      (s , pk , (pl , (t' , pv' , px)))
      ) =
      s' ,
      s ,
      ((c ∷ v , notmt) ,
        s'11≡ ,
        s12≡) ,
      pg .fst ,
      ph .fst ,
      pk .fst ,
      pl .fst ,
      s'11≡ ,
      s12≡
      where
      s11≡t11 : s .fst .fst ≡ t .fst .fst
      s11≡t11 =
        sym (⌈⌉→≡ y (s .fst .fst) (pk .snd))
        ∙ (⌈⌉→≡ y (t .fst .fst) py)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s'11≡ : s .fst .fst ++ c ∷ v ≡ s' .fst .fst
      s'11≡ = cong₂ _++_ s11≡t11 cv≡t12 ∙ sym (t .snd)

      s12≡ : s .fst .snd ≡ c ∷ v ++ s' .fst .snd
      s12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ x (t' .fst .snd) px)
            ∙ (⌈⌉→≡ x (s' .fst .snd) (ph .snd)))
    splittingTrichotomyG-inr-inr≅ ww .rightInv
      (w , x , y , z , ([] , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      Empty.rec (notmt refl)
    splittingTrichotomyG-inr-inr≅ ww .rightInv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))) =
      ΣPathP5 (
        sym (⌈⌉→≡ _ _ (pg .snd)) ,
        sym (⌈⌉→≡ _ _ (ph .snd)) ,
        sym (⌈⌉→≡ _ _ (pk .snd)) ,
        sym (⌈⌉→≡ _ _ (pl .snd)) ,
        refl ,
        ΣPathP5 (
          ΣPathP2 (
            refl ,
            ΣPathP3 (
              ΣPathPProp (λ _ → isLang⌈⌉ w (s .fst .fst)) refl ,
              Splitting≡
                (≡-×
                  (sym (⌈⌉→≡ y (s' .fst .fst) (pk .snd))
                    ∙ ⌈⌉→≡ y (t .fst .fst) py)
                  (⌈⌉→≡ _ _ pv)
                ) ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i) )
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i₁)) ∙
                      ⌈⌉→≡ y (t .fst .fst) py)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .fst)
                  )
                (mk⌈⌉ (s' .fst .fst))
                py ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i₁)) ∙
                      ⌈⌉→≡ y (t .fst .fst) py)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .snd)
                  )
                (mk⌈⌉ (c ∷ v))
                pv
              ) ,
            ΣPathPProp (λ _ → isLang⌈⌉ x (s .fst .snd)) refl
            ) ,
          refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ y (s' .fst .fst)) refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ z (s' .fst .snd)) refl ,
          Splitting≡
            (≡-×
              (⌈⌉→≡ _ _ pv')
              (sym (⌈⌉→≡ x _ (ph .snd)) ∙ ⌈⌉→≡ x _ px)
            ) ,
          ΣPathP (
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i₁)) ∙
                     ⌈⌉→≡ x (t' .fst .snd) px))
                   i .fst .fst)
                )
                (mk⌈⌉ (c ∷ v))
                pv' ,
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i))
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i₁)) ∙
                     ⌈⌉→≡ x (t' .fst .snd) px))
                   i .fst .snd)
                )
                (mk⌈⌉ (s .fst .snd))
                px
          ))
        )
      where
      s'11≡t11 : s' .fst .fst ≡ t .fst .fst
      s'11≡t11 =
        sym (⌈⌉→≡ y (s' .fst .fst) (pk .snd))
        ∙ (⌈⌉→≡ y (t .fst .fst) py)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s11≡ : s' .fst .fst ++ c ∷ v ≡ s .fst .fst
      s11≡ = cong₂ _++_ s'11≡t11 cv≡t12 ∙ sym (t .snd)

      s'12≡ : s' .fst .snd ≡ c ∷ v ++ s .fst .snd
      s'12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ x (t' .fst .snd) px)
            ∙ (⌈⌉→≡ x (s .fst .snd) (ph .snd)))
    splittingTrichotomyG-inr-inr≅ ww .leftInv
      (s , s' , ((c ∷ v , notmt) , split++) , p) =
      ΣPathP3 (
        refl ,
        refl ,
        ΣPathP2 (
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        ) ,
        ΣPathP5 (
          refl ,
          refl ,
          refl ,
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        )
      )

    splittingTrichotomyGΣ≅ :
      (w : String) →
      Iso
        (
        Σ[ s ∈ Splitting w ]
        Σ[ s' ∈ Splitting w ]
        Σ[ x ∈ splittingTrichotomyTy' w s s' ]
           splittingTrichotomyG w s s' x
         )
        (
        sameSplittingG w ⊎
        (secondPrefixG w ⊎ firstPrefixG w)
        )
    splittingTrichotomyGΣ≅ w =
      compIso
        (invIso Σ-assoc-Iso)
        (compIso
          (Σ-cong-iso-snd (λ _ →
            Σ⊎Iso
          ))
          (compIso
            (ΣDistR⊎Iso _ _ _)
            (⊎Iso
              (compIso Σ-assoc-Iso (splittingTrichotomyG-inl≅ w))
              (compIso
                (Σ-cong-iso-snd (λ _ →
                  Σ⊎Iso
                ))
                (compIso
                  (ΣDistR⊎Iso _ _ _)
                  (⊎Iso
                    (compIso Σ-assoc-Iso (splittingTrichotomyG-inr-inl≅ w))
                    (compIso Σ-assoc-Iso (splittingTrichotomyG-inr-inr≅ w))
                  )
                )
              )
            )
          )
        )

    ⊗&⊗parse≅ :
      (w : String) →
      Iso
        (((g ⊗ h) & (k ⊗ l)) w)
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd)))
    ⊗&⊗parse≅ w .fun ((s , pg , ph) , (s' , pk , pl)) =
      s , s' , pg , ph , pk , pl
    ⊗&⊗parse≅ w .inv (s , s' , pg , ph , pk , pl) =
      (s , pg , ph) , (s' , pk , pl)
    ⊗&⊗parse≅ w .rightInv _ = refl
    ⊗&⊗parse≅ w .leftInv _ = refl

    opaque
      unfolding _⊕_
      rtrt :
        (g ⊗ h) & (k ⊗ l)
        ≅
        sameSplittingG
        ⊕ (secondPrefixG ⊕ firstPrefixG)
      rtrt = pointwiseIso→≅ _ _
        (λ w →
          compIso
            (compIso
              (⊗&⊗parse≅ w)
              (compIso
                (wert w)
                (compIso
                  (invIso Σ-assoc-Iso)
                  (compIso
                    (Σ-cong-iso-snd (λ (s , s') →
                      invIso (Σ-contractFstIso
                        ((splittingTrichotomy' w s s') ,
                        (isPropSplittingTrichotomyTy' w s s' _)))
                    ))
                    Σ-assoc-Iso
                  ))
              ))
            (splittingTrichotomyGΣ≅ w)
        )

--   hjkl :
--     (g ⊗ h) & (k ⊗ l)
--     ≅
--     ((g & k) ⊗ (h & l)) ⊕
--     (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ w ∈ String ]
--       (((k & (g ⊗ ⌈ c ∷ w ⌉)) ⊗ l) & (g ⊗ ((⌈ c ∷ w ⌉ ⊗ l) & h)))) ⊕
--     (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ w ∈ String ]
--       (((g & (k ⊗ ⌈ c ∷ w ⌉)) ⊗ h) & (k ⊗ ((⌈ c ∷ w ⌉ ⊗ h) & l))))
--   hjkl = pointwiseIso→≅ _ _
--     (λ w →
--       {!!}
--     )

-- -- -- -- --   -- asdf :
-- -- -- -- --   --   (g : Grammar ℓg) →
-- -- -- -- --   --   (h : Grammar ℓh) →
-- -- -- -- --   --   (k : Grammar ℓk) →
-- -- -- -- --   --   (l : Grammar ℓl) →
-- -- -- -- --   --   (g ⊗ h) & (k ⊗ l)
-- -- -- -- --   --   ≅
-- -- -- -- --   --   ((g & k) ⊗ (h & l)) ⊕
-- -- -- -- --   --   (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ w ∈ String ]
-- -- -- -- --   --     (((k & (g ⊗ ⌈ c ∷ w ⌉)) ⊗ l) & (g ⊗ ((⌈ c ∷ w ⌉ ⊗ l) & h)))) ⊕
-- -- -- -- --   --   (⊕[ c ∈ ⟨ Alphabet ⟩ ] ⊕[ w ∈ String ]
-- -- -- -- --   --     (((g & (k ⊗ ⌈ c ∷ w ⌉)) ⊗ h) & (k ⊗ ((⌈ c ∷ w ⌉ ⊗ h) & l))))
-- -- -- -- --   -- asdf g h k l .fun w ((s , p , q) , (s' , p' , q')) =
-- -- -- -- --   --   Sum.rec
-- -- -- -- --   --     (λ (s₁≡ , s₂≡) →
-- -- -- -- --   --       ⊕-inl w
-- -- -- -- --   --         (s ,
-- -- -- -- --   --         (p , subst k (sym s₁≡) p') ,
-- -- -- -- --   --         (q , subst l (sym s₂≡) q'))
-- -- -- -- --   --     )
-- -- -- -- --   --     (λ { (([] , vnotmt) , the-Split++) →
-- -- -- -- --   --            Empty.rec (vnotmt refl)
-- -- -- -- --   --        ; ((c ∷ v , _) , the-Split++) →
-- -- -- -- --   --            Sum.rec
-- -- -- -- --   --              (λ the-split →
-- -- -- -- --   --                (⊕-inr ∘g ⊕-inl ∘g ⊕ᴰ-in c ∘g ⊕ᴰ-in v) w
-- -- -- -- --   --                  ((s' ,
-- -- -- -- --   --                    (p' ,
-- -- -- -- --   --                    ((s .fst .fst , c ∷ v) , sym (the-split .fst)) ,
-- -- -- -- --   --                      p ,
-- -- -- -- --   --                      internalize (c ∷ v)) , q') ,
-- -- -- -- --   --                  (s ,
-- -- -- -- --   --                  p ,
-- -- -- -- --   --                  (((_ , _) , (the-split .snd)) , ((internalize (c ∷ v)) , q')) , q)
-- -- -- -- --   --                  )
-- -- -- -- --   --              )
-- -- -- -- --   --              (λ the-split →
-- -- -- -- --   --                (⊕-inr ∘g ⊕-inr ∘g ⊕ᴰ-in c ∘g ⊕ᴰ-in v) w
-- -- -- -- --   --                  ((s , (p , ((_ , (sym (the-split .fst))) , (p' , (internalize (c ∷ v))))) , q) ,
-- -- -- -- --   --                  s' , (p' , (((_ , the-split .snd) , ((internalize (c ∷ v)) , q)) , q')))
-- -- -- -- --   --              )
-- -- -- -- --   --              the-Split++
-- -- -- -- --   --         })
-- -- -- -- --   --     (splittingTrichotomy w s s')
-- -- -- -- --   -- asdf g h k l .inv =
-- -- -- -- --   --   ⊕-elim
-- -- -- -- --   --     ((&-π₁ ,⊗ id) ,&p &-π₂ ,⊗ id ∘g ⊗&-distL)
-- -- -- -- --   --     (⊕-elim
-- -- -- -- --   --       (⊕ᴰ-elim (λ c → ⊕ᴰ-elim (λ w →
-- -- -- -- --   --         (id ,⊗ &-π₂) ,&p (&-π₁ ,⊗ id)
-- -- -- -- --   --         ∘g &-swap
-- -- -- -- --   --       )))
-- -- -- -- --   --       (⊕ᴰ-elim (λ c → ⊕ᴰ-elim (λ w →
-- -- -- -- --   --         (&-π₁ ,⊗ id) ,&p (id ,⊗ &-π₂)
-- -- -- -- --   --       )))
-- -- -- -- --   --     )
-- -- -- -- --   -- asdf g h k l .sec = the-sec
-- -- -- -- --   --   where
-- -- -- -- --   --   opaque
-- -- -- -- --   --     unfolding ⊕-elim _⊕_ &-π₁
-- -- -- -- --   --     the-sec : asdf g h k l .fun ∘g asdf g h k l .inv ≡ id
-- -- -- -- --   --     the-sec = {!!}
-- -- -- -- --   -- asdf g h k l .ret = the-ret
-- -- -- -- --   --   where
-- -- -- -- --   --   opaque
-- -- -- -- --   --     unfolding ⊕-elim _⊕_ &-π₁
-- -- -- -- --   --     the-ret : asdf g h k l .inv ∘g asdf g h k l .fun ≡ id
-- -- -- -- --   --     the-ret = funExt λ w → funExt λ
-- -- -- -- --   --       { ((s , p , q) , (s' , p' , q')) →
-- -- -- -- --   --       Sum.rec
-- -- -- -- --   --         (λ (s₁≡ , s₂≡) →
-- -- -- -- --   --           {!!}
-- -- -- -- --   --         )
-- -- -- -- --   --         {!!}
-- -- -- -- --   --         (splittingTrichotomy w s s')
-- -- -- -- --   --       }

-- -- -- -- -- -- hasUniqueSplit-char⊗ :
-- -- -- -- -- --   hasUniqueSplit char g
-- -- -- -- -- -- hasUniqueSplit-char⊗ w w' v v' =
-- -- -- -- -- --   {!!}
-- -- -- -- -- --   -- ⊕ᴰ-elim (λ c → ⊕ᴰ-elim λ c' →
-- -- -- -- -- --   --   ?
-- -- -- -- -- --   --   ∘g ?
-- -- -- -- -- --   --   ∘g ?
-- -- -- -- -- --   --   ∘g ?
-- -- -- -- -- --   --   ∘g ?
-- -- -- -- -- --   -- )
-- -- -- -- -- --   -- ∘g map⊕ᴰ (λ c → &⊕ᴰ-distR≅ .fun)
-- -- -- -- -- --   -- ∘g &⊕ᴰ-distL≅ .fun
-- -- -- -- -- --   -- ∘g (⊕ᴰ-distL .fun ∘g &⊕ᴰ-distL≅ .fun ,⊗ id) ,&p (⊕ᴰ-distL .fun ∘g &⊕ᴰ-distL≅ .fun ,⊗ id)
