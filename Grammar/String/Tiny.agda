-- Tinyness + other distribution laws for char
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Tiny (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Unambiguous Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet

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

char-⊗⊕-distL⁻ : (char ⊗ A) ⊕ (char ⊗ B) ⊢ char ⊗ (A ⊕ B)
char-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ inl) (id ,⊗ inr)

char-⊗⊕-distR⁻ : (A ⊗ char) ⊕ (B ⊗ char) ⊢ (A ⊕ B) ⊗ char
char-⊗⊕-distR⁻ = ⊕-elim (inl ,⊗ id) (inr ,⊗ id)

⌈⌉-⊗⊕-distL⁻ : (⌈ w ⌉ ⊗ A) ⊕ (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A ⊕ B)
⌈⌉-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ inl) (id ,⊗ inr)

⌈⌉-⊗⊕-distR⁻ : (A ⊗ ⌈ w ⌉) ⊕ (B ⊗ ⌈ w ⌉) ⊢ (A ⊕ B) ⊗ ⌈ w ⌉
⌈⌉-⊗⊕-distR⁻ = ⊕-elim (inl ,⊗ id) (inr ,⊗ id)

char-⊗⊕-distL≅ : char ⊗ (A ⊕ B) ≅ (char ⊗ A) ⊕ (char ⊗ B)
char-⊗⊕-distL≅ .fun = ⊗⊕-distL
char-⊗⊕-distL≅ .inv = char-⊗⊕-distL⁻
char-⊗⊕-distL≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distL≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distL≅ .inv ≡ id
    the-sec i w (Sum.inl p) = Sum.inl p
    the-sec i w (Sum.inr p) = Sum.inr p
char-⊗⊕-distL≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_ _⊗_
    the-ret : char-⊗⊕-distL≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distL≅ .fun ≡ id
    the-ret i w (s , p , Sum.inl q) = s , p , Sum.inl q
    the-ret i w (s , p , Sum.inr q) = s , p , Sum.inr q

char-⊗⊕-distR≅ : (A ⊕ B) ⊗ char ≅ (A ⊗ char) ⊕ (B ⊗ char)
char-⊗⊕-distR≅ .fun = ⊗⊕-distR
char-⊗⊕-distR≅ .inv = char-⊗⊕-distR⁻
char-⊗⊕-distR≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distR≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distR≅ .inv ≡ id
    the-sec i w (Sum.inl p) = Sum.inl p
    the-sec i w (Sum.inr p) = Sum.inr p
char-⊗⊕-distR≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distR _⊕_ _⊗_
    the-ret : char-⊗⊕-distR≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distR≅ .fun ≡ id
    the-ret i w (s , Sum.inl p , q) = s , Sum.inl p , q
    the-ret i w (s , Sum.inr p , q) = s , Sum.inr p , q

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
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
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
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
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
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
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
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
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
