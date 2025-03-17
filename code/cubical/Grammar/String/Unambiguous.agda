open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.List.More
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)

open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.Cartesian Alphabet
open import Grammar.Sum Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet

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
  unfolding literal
  char-length1 : ∀ w → char w → length w ≡ 1
  char-length1 [] (c , p) = Empty.rec (¬nil≡cons p)
  char-length1 (x ∷ []) (c , p) = refl
  char-length1 (x ∷ x₁ ∷ w) (c , p) = Empty.rec (¬cons≡nil (cons-inj₂ p))

module _ (c : ⟨ Alphabet ⟩) where
  literal→char : ＂ c ＂ ⊢ char
  literal→char = σ c

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


