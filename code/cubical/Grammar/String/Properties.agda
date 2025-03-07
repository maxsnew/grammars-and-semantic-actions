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
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

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
    (p : (char ⊗ A) w) →
    (q : (char ⊗ B) w) →
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
      (p : (＂ c ＂ ⊗ A) w) →
      (q : (＂ c ＂ ⊗ B) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalL {A = A} {c = c} w p q =
      unique-splitting-charL w ((literal→char c  ,⊗ id) w p ) ((literal→char c ,⊗ id) w q)

  unique-splitting-charR :
    (w : String) →
    (p : (A ⊗ char) w) →
    (q : (B ⊗ char) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charR {A = A} w (s , p , (c , q)) (s' , p' , (c' , q')) =
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
      (p : (A ⊗ ＂ c ＂) w) →
      (q : (B ⊗ ＂ c ＂) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalR {A = A} {c = c} w p q =
      unique-splitting-charR w ((id ,⊗ literal→char c) w p ) ((id ,⊗ literal→char c) w q)


module _ (x : String) where
  opaque
    unfolding the-split _⊗_ literal
    unique-splitting-⌈⌉L :
      (w : String) →
      (p : (⌈ x ⌉ ⊗ A) w) →
      (q : (⌈ x ⌉ ⊗ B) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-⌈⌉L w (s , px , q) (s' , px' , q') =
      ≡-× 11≡
        (
        sym (dropLength++ (s' .fst .fst))
        ∙ cong (drop (length (s' .fst .fst)))
          (cong (_++ s .fst .snd) (sym 11≡)
          ∙ sym (s .snd) ∙ (s' .snd))
        ∙ dropLength++ (s' .fst .fst)
        )
        where
        11≡ : s .fst .fst ≡ s' .fst .fst
        11≡ = (sym (⌈⌉→≡ x (s .fst .fst) px) ∙ ⌈⌉→≡ x (s' .fst .fst) px')

    unique-splitting-⌈⌉R :
      (w : String) →
      (p : (A ⊗ ⌈ x ⌉) w) →
      (q : (B ⊗ ⌈ x ⌉) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-⌈⌉R w (s , q , px) (s' , q' , px') =
      ≡-×
        (
        sym (dropBackLength++ (s .fst .fst) (s .fst .snd))
        ∙ cong (dropBack (length (s .fst .snd)))
           (sym (s .snd) ∙ (s' .snd) ∙ cong (s' .fst .fst ++_) (sym 12≡))
        ∙ dropBackLength++ (s' .fst .fst) (s .fst .snd)
        )
        12≡
        where
        12≡ : s .fst .snd ≡ s' .fst .snd
        12≡ = (sym (⌈⌉→≡ x (s .fst .snd) px) ∙ ⌈⌉→≡ x (s' .fst .snd) px')

module _
  {A : Grammar ℓA}
  (isLang-A : isLang A)
  where
  module _ {c : ⟨ Alphabet ⟩} where
    opaque
      unfolding _⊗_ the-split
      isLang-lit⊗lang : isLang (＂ c ＂ ⊗ A)
      isLang-lit⊗lang w x y =
        Σ≡Prop
          (λ s → isProp× (isLangLiteral c (s .fst .fst)) (isLang-A (s .fst .snd)))
          (Splitting≡ (unique-splitting-literalL w x y))

      isLang-lang⊗lit : isLang (A ⊗ ＂ c ＂)
      isLang-lang⊗lit w x y =
        Σ≡Prop
          (λ s → isProp× (isLang-A (s .fst .fst)) (isLangLiteral c (s .fst .snd)))
          (Splitting≡ (unique-splitting-literalR w x y))
  opaque
    unfolding _⊗_ the-split
    isLang-char⊗lang : isLang (char ⊗ A)
    isLang-char⊗lang w x y =
      Σ≡Prop
        (λ s → isProp× (isLang-char (s .fst .fst)) (isLang-A (s .fst .snd)))
        (Splitting≡ (unique-splitting-charL w x y))

    isLang-lang⊗char : isLang (A ⊗ char)
    isLang-lang⊗char w x y =
      Σ≡Prop
        (λ s → isProp× (isLang-A (s .fst .fst)) (isLang-char (s .fst .snd)))
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

char-⊗⊕-distL⁻ : (char ⊗ A) ⊕ (char ⊗ B) ⊢ char ⊗ (A ⊕ B)
char-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ ⊕-inl) (id ,⊗ ⊕-inr)

char-⊗⊕-distR⁻ : (A ⊗ char) ⊕ (B ⊗ char) ⊢ (A ⊕ B) ⊗ char
char-⊗⊕-distR⁻ = ⊕-elim (⊕-inl ,⊗ id) (⊕-inr ,⊗ id)

⌈⌉-⊗⊕-distL⁻ : (⌈ w ⌉ ⊗ A) ⊕ (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A ⊕ B)
⌈⌉-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ ⊕-inl) (id ,⊗ ⊕-inr)

⌈⌉-⊗⊕-distR⁻ : (A ⊗ ⌈ w ⌉) ⊕ (B ⊗ ⌈ w ⌉) ⊢ (A ⊕ B) ⊗ ⌈ w ⌉
⌈⌉-⊗⊕-distR⁻ = ⊕-elim (⊕-inl ,⊗ id) (⊕-inr ,⊗ id)

char-⊗⊕-distL≅ : char ⊗ (A ⊕ B) ≅ (char ⊗ A) ⊕ (char ⊗ B)
char-⊗⊕-distL≅ .fun = ⊗⊕-distL
char-⊗⊕-distL≅ .inv = char-⊗⊕-distL⁻
char-⊗⊕-distL≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distL≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distL≅ .inv ≡ id
    the-sec i w (inl p) = inl p
    the-sec i w (inr p) = inr p
char-⊗⊕-distL≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_ _⊗_
    the-ret : char-⊗⊕-distL≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distL≅ .fun ≡ id
    the-ret i w (s , p , inl q) = s , p , inl q
    the-ret i w (s , p , inr q) = s , p , inr q

char-⊗⊕-distR≅ : (A ⊕ B) ⊗ char ≅ (A ⊗ char) ⊕ (B ⊗ char)
char-⊗⊕-distR≅ .fun = ⊗⊕-distR
char-⊗⊕-distR≅ .inv = char-⊗⊕-distR⁻
char-⊗⊕-distR≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distR≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distR≅ .inv ≡ id
    the-sec i w (inl p) = inl p
    the-sec i w (inr p) = inr p
char-⊗⊕-distR≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distR _⊕_ _⊗_
    the-ret : char-⊗⊕-distR≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distR≅ .fun ≡ id
    the-ret i w (s , inl p , q) = s , inl p , q
    the-ret i w (s , inr p , q) = s , inr p , q

opaque
  unfolding _⊗_ _&_ the-split literal
  char-⊗&-distL⁻ :
    (char ⊗ A) & (char ⊗ B) ⊢ char ⊗ (A & B)
  char-⊗&-distL⁻ {B = B} w ((s , p , q) , (s' , p' , q')) =
    s , (p , (q , subst B s≡ q'))
    where
    s≡ : s' .fst .snd ≡ s .fst .snd
    s≡ = cons-inj₂
      (cong (_++ s' .fst .snd) (sym (p' .snd))
      ∙ sym (s' .snd)
      ∙ s .snd
      ∙ cong (_++ s .fst .snd) (p .snd)
      )

  ⌈⌉-⊗&-distL⁻ :
    (⌈ w ⌉ ⊗ A) & (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A & B)
  ⌈⌉-⊗&-distL⁻ {w = w} {A = A} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p , q , subst B 12≡ q')
    where
    s≡ : same-splits
      {A = ⌈ w ⌉} {B = A} {C = ⌈ w ⌉} {D = B}
      {w = λ _ → w'}
      (s , p , q)
      (s' , p' , q')
    s≡ =
      unique-splitting-⌈⌉L
        w
        {A = A}
        {B = B}
        w'
        (s , p , q)
        (s' , p' , q')

    12≡ : s' .fst .snd ≡ s .fst .snd
    12≡ = sym (cong snd s≡)

  char-⊗&-distR⁻ :
    (A ⊗ char) & (B ⊗ char) ⊢ (A & B) ⊗ char
  char-⊗&-distR⁻ {A = A} {B = B} w ((s , p , q) , (s' , p' , q')) =
    s ,
    ((p ,
    subst B
      (cong (λ z → z .fst)
      (sym (unique-splitting-charR {A = A} {B = B}
        w (s , p , q) (s' , p' , q')))) p') , q)

  ⌈⌉-⊗&-distR⁻ :
    (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉) ⊢ (A & B) ⊗ ⌈ w ⌉
  ⌈⌉-⊗&-distR⁻ {A = A} {w = w} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p ,
      (subst B
        (cong fst (sym (
          unique-splitting-⌈⌉R
            w
            {A = A}
            {B = B}
            w'
            (s , p , q)
            (s' , p' , q')
        )))
        p')
      ) , q

char-⊗&-distR≅ : (A & B) ⊗ char ≅ (A ⊗ char) & (B ⊗ char)
char-⊗&-distR≅ .fun = ⊗&-distR
char-⊗&-distR≅ .inv = char-⊗&-distR⁻
char-⊗&-distR≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR
    the-sec : char-⊗&-distR≅ {A = A} {B = B} .fun ∘g char-⊗&-distR≅ .inv ≡ id
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
    the-ret : char-⊗&-distR≅ {A = A} {B = B} .inv ∘g char-⊗&-distR≅ .fun ≡ id
    the-ret {B = B} = funExt λ w → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          (ΣPathP (
            refl ,
            symP (transport-filler _ (p .snd .fst .snd)
            ∙ cong (λ z → transport (λ i → B (z i)) (p .snd .fst .snd))
              (isSetString _ _ _ _))
          )) ,
          refl
        ))
      )

⌈⌉-⊗&-distR≅ : (A & B) ⊗ ⌈ w ⌉ ≅ (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉)
⌈⌉-⊗&-distR≅ .fun = ⊗&-distR
⌈⌉-⊗&-distR≅ {w = w} .inv = ⌈⌉-⊗&-distR⁻ {w = w}
⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .sec = the-sec
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR
    the-sec :
      ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .fun
      ∘g ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .inv ≡ id
    the-sec = funExt λ w' → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          Splitting≡
            (unique-splitting-⌈⌉R w w' (p .fst) (p .snd))
            ,
          ΣPathP (
            (symP (transport-filler _ (p .snd .snd .fst))) ,
            (isProp→PathP (λ i → isLang⌈⌉ w _) _ _)
          )
        ))
      )
⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .ret = the-ret
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR
    the-ret :
      ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .inv
      ∘g ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .fun ≡ id
    the-ret = funExt λ w → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          (ΣPathP (
            refl ,
            symP (transport-filler _ (p .snd .fst .snd)
            ∙ cong (λ z → transport (λ i → B (z i)) (p .snd .fst .snd))
              (isSetString _ _ _ _))
          )) ,
          refl
        ))
      )

⊤→string : ⊤ ⊢ string
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤→string' : ⊤ ⊢ string
⊤→string' w _ = mkstring' w

⊤*→string : ∀ {ℓA} → ⊤* {ℓA} ⊢ string
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

string≅stringL : string ≅ stringL
string≅stringL = *≅*L char

string-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ string
string-intro = ⊤→string ∘g ⊤-intro

stringL-intro : ∀ {ℓA} {A : Grammar ℓA} → A ⊢ stringL
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

totallyParseable' : Grammar ℓA → Type (ℓ-suc ℓA)
totallyParseable' {ℓA = ℓA} A =
  Σ[ B ∈ Grammar ℓA ] StrongEquivalence (A ⊕ B) string

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

  -- There's almost surely a way to do this in the logic
  -- but I am just going to axiomatize it
  opaque
    unfolding literal _⊗_ _&_
    same-first' :
      startsWith c & startsWith c' ⊢
        ⊕[ x ∈ (c ≡ c') ] startsWith c
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

firstChar≅ : A ≅ (A & ε) ⊕ (⊕[ c ∈ ⟨ Alphabet ⟩ ] (A & startsWith c))
firstChar≅ =
  &string-split≅
  ≅∙ ⊕≅ id≅ (&≅ id≅ ⊕ᴰ-distL ≅∙ &⊕ᴰ-distR≅)

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
      nil → ⊕ᴰ-in [] ∘g lowerG ∘g lowerG
    ; cons →
      ⊕ᴰ-elim (λ w → ⊕ᴰ-elim (λ c → ⊕ᴰ-in (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
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
  (Split++ w x y z u ⊎ Split++ y z w x u) →
  Grammar ℓ-zero
Split++⌈⌉ w x y z u (inl the-split) =
  ⌈ w ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ z ⌉
Split++⌈⌉ w x y z u (inr the-split) =
  ⌈ y ⌉ ⊗ ⌈ u ⌉ ⊗ ⌈ x ⌉

