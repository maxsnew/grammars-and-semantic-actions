open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Base (Alphabet : hSet ℓ-zero)where

import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List hiding (rec)
import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Grammar.SequentialUnambiguity.FollowLast Alphabet
open import Grammar.PropositionalTruncation.Base Alphabet
open import Term Alphabet

open import Cubical.Foundations.Powerset.More

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence
open Powerset ⟨ Alphabet ⟩

sequentiallyUnambiguous :
  Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
sequentiallyUnambiguous A B =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast A ⟩ Sum.⊎ ⟨ c ∉First B ⟩

syntax sequentiallyUnambiguous A B = A ⊛ B

module _
  (A : Grammar ℓA)
  (c : ⟨ Alphabet ⟩)
  (c∉FLA : ⟨ c ∉FollowLast A ⟩)
  (disc : Discrete ⟨ Alphabet ⟩)
  where
  ∉FollowLast→⊛ : A ⊛ startsWith c
  ∉FollowLast→⊛ c' =
    decRec
      (J (λ c' c≡c' → ⟨ c' ∉FollowLast A ⟩ Sum.⊎ (disjoint (startsWith c') (startsWith c)))
        (Sum.inl (c∉FLA)))
      (λ c≢c' → Sum.inr (⊕ᴰ-elim (λ c'≡c → Empty.rec (c≢c' (sym c'≡c))) ∘g same-first c' c))
      (disc c c')

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (C : Grammar ℓC)
  (seq-unambig : A ⊛ B)
  (¬nullB : ⟨ ¬Nullable B ⟩)
  where
  ⊛-⊗l : A ⊛ (B ⊗ C)
  ⊛-⊗l c =
    Sum.map (λ x → x) (∉First⊗l ¬nullB) (seq-unambig c)

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (C : Grammar ℓC)
  (seq-unambig-B : A ⊛ B)
  (seq-unambig-C : A ⊛ C)
  where
  ⊛-⊗ : A ⊛ (B ⊗ C)
  ⊛-⊗ c =
    Sum.rec
      (λ x → Sum.inl x)
      (λ c∉FB →
        Sum.rec
          Sum.inl
          (λ c∉FC → Sum.inr (∉First⊗ c∉FB c∉FC))
          (seq-unambig-C c)
      )
      (seq-unambig-B c)

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  (seq-unambig : A ⊛ B)
  (f : C ⊢ B)
  where

  ⊛∘g-r : A ⊛ C
  ⊛∘g-r c = Sum.map (λ x → x) (∉First∘g f) (seq-unambig c)

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  (seq-unambig : A ⊛ B)
  (f : C ⊢ A)
  where

  ⊛∘g-l : C ⊛ B
  ⊛∘g-l c = Sum.map (∉FollowLast∘g f) (λ x → x) (seq-unambig c)

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (C : Grammar ℓC)
  (seq-unambig : A ⊛ B)
  where
  ⊛-& : A ⊛ (B & C)
  ⊛-& c = ⊛∘g-r seq-unambig π₁ c

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (seq-unambig : A ⊛ B)
  where
  ⊛-* : A ⊛ (B *)
  ⊛-* c =
    Sum.map
      (λ x → x)
      ∉First*
      (seq-unambig c)

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (C : Grammar ℓC)
  (seq-unambig-B : A ⊛ B)
  (seq-unambig-C : A ⊛ C)
  where

  private
    uninhabitedFirstPrefixG :
      firstPrefixG A B A C ⊢ ⊥
    uninhabitedFirstPrefixG =
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉FlA →
              ⊥⊗
              ∘g (c∉FlA ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((π₁ ∘g π₁) ,⊗ π₂) ,&p (π₁ ,⊗ π₂)
            )
            (λ c∉FC →
              ⊗⊥
              ∘g id ,⊗ (c∉FC ∘g &-swap)
              ∘g id ,⊗ (π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g π₂
            )
            (seq-unambig-C c)
        })))))

    uninhabitedSecondPrefixG :
      secondPrefixG A B A C ⊢ ⊥
    uninhabitedSecondPrefixG =
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉FlA →
              ⊥⊗
              ∘g (c∉FlA ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((π₁ ∘g π₁) ,⊗ π₂) ,&p (π₁ ,⊗ π₂)
            )
            (λ c∉FB →
              ⊗⊥
              ∘g id ,⊗ (c∉FB ∘g &-swap)
              ∘g id ,⊗ (π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g π₂
            )
            (seq-unambig-B c)
        })))))

  ⊗&-distL≅ :
    (A ⊗ B) & (A ⊗ C)
    ≅
    (A & A) ⊗ (B & C)
  ⊗&-distL≅ =
    ⊗&-split A B A C
    ≅∙ ⊕≅
      id≅
      (
      (⊕≅
        (uninhabited→≅⊥ uninhabitedSecondPrefixG)
        (uninhabited→≅⊥ uninhabitedFirstPrefixG)
      )
      ≅∙ ⊥⊕≅ ⊥
      )
    ≅∙ ⊕-swap≅
    ≅∙ ⊥⊕≅ (A & A ⊗ B & C)

seq-unambig-εL : ε ⊛ A
seq-unambig-εL c = Sum.inl ((disjoint-ε-char+ ∘g id ,&p (literal→char c ,⊗ id ∘g ⊗-unit-l)) ∘g &-swap)

seq-unambig-εR : A ⊛ ε
seq-unambig-εR c = Sum.inr (disjoint-ε-char+ ∘g id ,&p literal→char c ,⊗ id ∘g &-swap)

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (seq-unambig : A ⊛ B)
  (¬nullB : ⟨ ¬Nullable B ⟩)
  where

  ⊛→must-split : disjoint A (A ⊗ B ⊗ string)
  ⊛→must-split =
    ⊕ᴰ-elim (λ c →
      Sum.rec
        (λ c∉FL →
          c∉FL
          ∘g &-swap
          ∘g id ,&p (id ,⊗ (id ,⊗ string-intro ∘g ⊗-assoc⁻ ∘g π₂ ,⊗ id))
        )
        (λ c∉FB →
          ⊗⊥
          ∘g id ,⊗ (⊥⊗ ∘g (c∉FB ∘g &-swap) ,⊗ id)
          ∘g π₂
        )
        (seq-unambig c)
    )
    ∘g &⊕ᴰ-distR≅ .fun
    ∘g id ,&p
      (⊕ᴰ-distR .fun
      ∘g id ,⊗
        (⊕ᴰ-distL .fun
        ∘g (⊥⊕≅ _ .fun
            ∘g ((¬nullB ∘g &-swap) ,⊕p id)
            ∘g firstChar≅ .fun) ,⊗ id))

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (C : Grammar ℓC)
  (D : Grammar ℓD)
  (seq-unambig : A ⊛ B)
  (¬nullB : ⟨ ¬Nullable B ⟩)
  where

  factor⊗3≅ :
    (A ⊗ B ⊗ C) & (A ⊗ B ⊗ D)
    ≅
    (A & A) ⊗ ((B ⊗ C) & (B ⊗ D))
  factor⊗3≅ =
    ⊗&-distL≅ A (B ⊗ C) (B ⊗ D)
      (⊛-⊗l A B C seq-unambig ¬nullB)
      (⊛-⊗l A B D seq-unambig ¬nullB)

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (¬nullA : ⟨ ¬Nullable A ⟩)
  (¬nullB : ⟨ ¬Nullable B ⟩)
  (seq-unambig : A ⊛ B)
  (c : ⟨ Alphabet ⟩)
  (c∉FLB : ⟨ c ∉FollowLast B ⟩)
  where
  ∉FollowLast-⊗¬null : ⟨ c ∉FollowLast (A ⊗ B) ⟩
  ∉FollowLast-⊗¬null =
    ⊗⊥
    ∘g id ,⊗ c∉FLB
    ∘g ⊗&-distL≅
         A
         (B ⊗ ＂ c ＂ ⊗ string)
         B
         (⊛-⊗l A B (＂ c ＂ ⊗ string) seq-unambig ¬nullB)
         seq-unambig
         .fun
    ∘g ⊗-assoc⁻ ,&p id

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (¬nullA : ⟨ ¬Nullable A ⟩)
  (seq-unambig : A ⊛ B)
  (c : ⟨ Alphabet ⟩)
  (c∉FLA : ⟨ c ∉FollowLast A ⟩)
  (c∉FLB : ⟨ c ∉FollowLast B ⟩)
  (c∉FB : ⟨ c ∉First B ⟩)
  (disc : Discrete ⟨ Alphabet ⟩)
  where
  ∉FollowLast-⊗null : ⟨ c ∉FollowLast (A ⊗ B) ⟩
  ∉FollowLast-⊗null =
    ⊕-elim
      (⊗⊥
      ∘g id ,⊗ c∉FB
      ∘g ⊗&-distL≅ A (＂ c ＂ ⊗ string) B (∉FollowLast→⊛ A c c∉FLA disc) seq-unambig .fun
      ∘g ((⊗-unit-r ∘g id ,⊗ π₂) ,⊗ id ∘g ⊗-assoc) ,&p id)
      (⊕-elim
        (⊛→must-split A (B & char +) A⊛B+ ¬nullB+
        ∘g id ,&p id ,⊗ id ,⊗ string-intro
        ∘g &-swap
        ∘g id ,&p (⊗-unit-r ∘g id ,⊗ π₂))
        (∉FollowLast-⊗¬null A (B & (char +)) ¬nullA ¬nullB+ A⊛B+ c c∉FLB+
        ∘g ⊗-assoc ,&p id)
      ∘g &⊕-distL
      ∘g id ,&p (⊗⊕-distL ∘g id ,⊗ &string-split≅ .fun))
    ∘g &⊕-distR
    ∘g (⊗⊕-distL ∘g id ,⊗ (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ∘g ⊗-assoc⁻) ,&p id
    where
    A⊛B+ : A ⊛ (B & (char +))
    A⊛B+ = ⊛-& A B (char +) seq-unambig

    ¬nullB+ : ⟨ ¬Nullable (B & (char +)) ⟩
    ¬nullB+ = ¬Nullable∘g π₂ ¬Nullable-char+

    c∉FLB+ : ⟨ c ∉FollowLast (B & (char +)) ⟩
    c∉FLB+ = ∉FollowLast∘g π₁ c∉FLB

module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  (c : ⟨ Alphabet ⟩)
  (c∉FLA : ⟨ c ∉FollowLast A ⟩)
  (c∉FLB : ⟨ c ∉FollowLast B ⟩)
  (¬nullB∨c∉FA : ⟨ ¬Nullable B ⟩ Sum.⊎ ⟨ c ∉First A ⟩)
  (¬nullA∨c∉FB : ⟨ ¬Nullable A ⟩ Sum.⊎ ⟨ c ∉First B ⟩)
  (sep : A # B)
  where
  ∉FollowLast-⊕ : ⟨ c ∉FollowLast (A ⊕ B) ⟩
  ∉FollowLast-⊕ =
    ⊕-elim
      (⊕-elim
        c∉FLA
        (Sum.rec
          (λ ¬nullB →
            #→disjoint
              (#⊗l
                (¬Nullable∘g π₂ ¬Nullable-char+)
                (sym# (#∘g2 π₁ π₁ sep))
              )
              (Sum.inl (¬Nullable⊗l ¬Nullable-&char+))
            ∘g (¬Nullable&char+≅ ¬nullB .fun ,⊗ id ∘g π₁) ,& π₂ ,& (¬Nullable→char+ (¬Nullable⊗l ¬nullB) ∘g π₁)
          )
          (λ c∉FA →
            ⊕-elim
              (c∉FA
              ∘g (⊗-unit-l ∘g π₂ ,⊗ id) ,&p id)
              (#→disjoint (#⊗l ¬Nullable-&char+ (#∘g π₁ (sym# sep))) (Sum.inl (¬Nullable⊗l ¬Nullable-&char+)))
            ∘g &⊕-distR
            ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id
          )
          ¬nullB∨c∉FA)
      ∘g &⊕-distR)
      (⊕-elim
        (Sum.rec
          (λ ¬nullA →
            #→disjoint
              (#⊗l
                (¬Nullable∘g π₂ ¬Nullable-char+)
                (#∘g2 π₁ π₁ sep)
              )
              (Sum.inl (¬Nullable⊗l ¬Nullable-&char+))
            ∘g (¬Nullable&char+≅ ¬nullA .fun ,⊗ id ∘g π₁) ,& π₂ ,& (¬Nullable→char+ (¬Nullable⊗l ¬nullA) ∘g π₁)
          )
          (λ c∉FB →
            ⊕-elim
              (c∉FB
              ∘g (⊗-unit-l ∘g π₂ ,⊗ id) ,&p id)
              (#→disjoint (#⊗l ¬Nullable-&char+ (#∘g π₁ sep)) (Sum.inl (¬Nullable⊗l ¬Nullable-&char+)))
            ∘g &⊕-distR
            ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id
          )
          ¬nullA∨c∉FB)
        c∉FLB
      ∘g &⊕-distR)
    ∘g &⊕-distL
    ∘g ⊗⊕-distR ,&p id

module _
  (A : Grammar ℓA)
  (c : ⟨ Alphabet ⟩)
  (c∉FA : ⟨ c ∉First A ⟩)
  (c∉FLA : ⟨ c ∉FollowLast A ⟩)
  (¬nullA : ⟨ ¬Nullable A ⟩)
  (seq-unambig : A ⊛ A)
  (disc : Discrete ⟨ Alphabet ⟩)
  where

-- Goal: show that A * & (A * ⊗ c ⊗ ⊤) ⊢ ⊥ assuming
-- - A & (A ⊗ c ⊗ ⊤) ⊢ ⊥
--   - c not in follow last of A
-- - A & (c ⊗ ⊤) ⊢ ⊥
--   - c not in first set of A
-- - For all c', either A & (c' ⊗ ⊤) ⊢ ⊥ or A & (A ⊗ c' ⊗ ⊤) ⊢ ⊥
--   - A is sequentially unambiguous with itself, which we may write as A ⊛ A.
--
-- The proof below goes rough as follows
--
-- Build a term A * ⊢ ¬(A * ⊗ c ⊗ ⊤) & (A *)
--
-- Here the ε case is easy.
-- Then inductively show that A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *)) ⊢ ¬(A * ⊗ c ⊗ ⊤) & (A *)
--
-- Constructing the A * on the right is straightforward so it suffices to show
--   A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *)) ⊢ ¬(A * ⊗ c ⊗ ⊤)
--
-- This proceeds roughly as
--
-- A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *)) ⊢ ¬(A * ⊗ c ⊗ ⊤)
-- iff
-- (A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *))) & (A * ⊗ c ⊗ ⊤) ⊢ ⊥
--
-- (A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *))) & (A * ⊗ c ⊗ ⊤) ⊢ ⊥
--
-- Reason if the right A * is empty or not,
-- and conclude it can't be because that would put c in the first set of A
-- which we've assumed is not the case.
--
-- Thus the rightmost A * is really a (A *) & (char +), which is isomorphic to A ⊗ A*
--
-- So we show
-- (A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *))) & (A ⊗ A * ⊗ c ⊗ ⊤) ⊢ ⊥
-- by noting that A and (¬(A * ⊗ c ⊗ ⊤) & (A *)) are sequentially unambiguous,
-- so are A and (A * ⊗ c ⊗ ⊤)
-- Thus we factor as
--
-- (A ⊗ (¬(A * ⊗ c ⊗ ⊤) & (A *))) & (A ⊗ A * ⊗ c ⊗ ⊤)
-- ≅ (A & A) ⊗ ((¬(A * ⊗ c ⊗ ⊤) & (A *)) & (A * ⊗ c ⊗ ⊤))
--
-- From which we can look at the right side of the tensor,
-- project out the ¬(A * ⊗ c ⊗ ⊤) and apply it reach the desired contradiction

  private
    nonmt-* : (A *) & (char +) ≅ A ⊗ (A *)
    nonmt-* =
      &≅ (*≅ε⊕A⊗A* A) id≅
      ≅∙ &⊕-distR≅
      ≅∙ ⊕≅ (uninhabited→≅⊥ disjoint-ε-char+) id≅
      ≅∙ ⊕≅
        (sym≅
          (uninhabited→≅⊥
            (disjoint-ε-char+
            ∘g id ,&p ¬Nullable→char+ (¬Nullable⊗l ¬nullA)
            ∘g &-swap
            )
          )
        )
        id≅
      ≅∙ sym≅ &string-split≅

    nil-pf : ε ⊢ ¬G FollowLastG (A *) c
    nil-pf =
      ⇒-intro
        (disjoint-ε-char+
         ∘g id ,&p ((char+⊗r→char+ ∘g id ,⊗ startsWith→char+) ∘g π₁))

    the-alg : Algebra (*Ty A) (λ _ → (¬G FollowLastG (A *) c) & (A *))
    the-alg _ =
      ⊕ᴰ-elim λ {
          nil →
            nil-pf ,& NIL
            ∘g lowerG ∘g lowerG
        ; cons →
           the-cons-pf ,& (CONS ∘g id ,⊗ π₂)
           ∘g lowerG ,⊗ lowerG
      }
      where
      the-⊛-* : A ⊛ (A *)
      the-⊛-* = ⊛-* A A seq-unambig

      the-cons-pf : A ⊗ ¬G FollowLastG (A *) c & (A *) ⊢ ¬G FollowLastG (A *) c
      the-cons-pf =
        ⇒-intro
         (⊕-elim
           (π₂
           ∘g id ,&p (∉First* c∉FA ∘g (⊗-unit-l ∘g π₂ ,⊗ id) ,&p id))
           (⊕-elim
             (¬Nullable-char+
             ∘g (π₂ ∘g π₂) ,& ((char+⊗r→char+ ∘g id ,⊗ startsWith→char+) ∘g π₂ ∘g π₁))
             (⊗⊥
             ∘g id ,⊗ (⇒-app ∘g (π₁ ∘g π₁ ∘g π₁) ,& (π₂ ,&p id))
             ∘g ⊗&-distL≅ _ _ _
                  (⊛∘g-r the-⊛-* (π₂ ∘g π₁))
                  the-⊛-*
                  .fun
             ∘g (π₁ ,⊗ id ∘g
                 ⊗&-distL≅ _ _ _
                  (⊛∘g-r the-⊛-* π₂)
                  (⊛-⊗ A (A *) (startsWith c) the-⊛-* (∉FollowLast→⊛ _ _ c∉FLA disc)) .fun
                  ∘g id ,&p ⊗-assoc⁻) ,&p nonmt-* .fun
             )
           ∘g &⊕-distL
           ∘g id ,&p &string-split≅ .fun
           ∘g &-assoc
           ∘g id ,&p ((nonmt-* .fun ,⊗ id) ,&p id))
         ∘g &⊕-distL
         ∘g id ,&p (&⊕-distR ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id)
         )

  ∉FollowLast-* : ⟨ c ∉FollowLast (A *) ⟩
  ∉FollowLast-* =
    ⇒-app
    ∘g (π₁ ∘g π₂) ,& (id ,&p π₂)
    ∘g id ,&p rec _ the-alg _
