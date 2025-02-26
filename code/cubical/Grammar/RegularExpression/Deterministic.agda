{-- Deterministic Regular Expressions --}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset.More

open import Cubical.Data.FinSet
open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.Powerset.Base

open import Grammar Alphabet hiding (k)
open import Grammar.Sum.Properties Alphabet
open import Grammar.Negation.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.LinearProduct.SplittingTrichotomy Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Grammar.PropositionalTruncation.Base Alphabet

open import Grammar.SequentialUnambiguity Alphabet
open import Grammar.Subgrammar.Base Alphabet renaming (true to trueG ; false to falseG)

open import Term Alphabet
open import Helper

private
  variable
    c : ⟨ Alphabet ⟩

open StrongEquivalence

open Powerset ⟨ Alphabet ⟩
open PowersetOverSet (Alphabet .snd)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  data DetReg : RegularExpression → ℙ → ℙ → Bool → Type (ℓ-suc ℓ-zero)

  sound¬Nullable :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    if b then
    ⟨ ¬Nullable ⟦ r ⟧r ⟩ else
    ε ⊢ ⟦ r ⟧r

  sound¬First :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    (c : ⟨ Alphabet ⟩) →
    c ∈ ¬F →
    ⟨ c ∉First ⟦ r ⟧r ⟩

  sound¬FollowLast :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    (c : ⟨ Alphabet ⟩) →
    c ∈ ¬FL →
    ⟨ c ∉FollowLast ⟦ r ⟧r ⟩

  unambiguousDR :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    unambiguous ⟦ r ⟧r

  -- A deterministic regular expression is parametrized
  -- a regular expression r and
  -- the complement of its follow last set,
  -- the complement of its first last set,
  -- and the negation of its nullability.
  -- By negating each of these, the indices are prop valued,
  -- whereas if we used the nonnegated versions it would not
  -- be prop valued
  data DetReg where
    εdr : DetReg εr ⊤ℙ ⊤ℙ false
    ⊥dr : DetReg ⊥r ⊤ℙ ⊤ℙ true
    ＂_＂dr :
      (c : ⟨ Alphabet ⟩) →
      DetReg (＂ c ＂r) ⊤ℙ (¬ℙ ⟦ c ⟧ℙ) true
    _⊗DR[_]_ :
      ∀ {r r' : RegularExpression} →
      {¬FL ¬FL' ¬F ¬F' : ℙ} →
      {b' : Bool} →
      (dr : DetReg r ¬FL ¬F true) →
      (seq-unambig :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬FL) ⊎ (c ∈ ¬F')
      ) →
      (dr' : DetReg r' ¬FL' ¬F' b') →
      DetReg
        (r ⊗r r')
        (if b' then ¬FL' else ¬FL ∩ℙ ¬F' ∩ℙ ¬FL')
        ¬F
        true
    _⊕DR[_]_ :
      ∀ {r r' : RegularExpression} →
      {¬FL ¬FL' ¬F ¬F' : ℙ} →
      {b b' : Bool} →
      {notBothNull : b or b' Eq.≡ true} →
      (dr : DetReg r ¬FL ¬F b) →
      (sep :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬F) ⊎ (c ∈ ¬F')
      ) →
      (dr' : DetReg r' ¬FL' ¬F' b') →
      DetReg
        (r ⊕r r')
        (¬FL ∩ℙ
        ¬FL' ∩ℙ
        (if (b and b') then ⊤ℙ else ¬F ∩ℙ ¬F')
        )
        (¬F ∩ℙ ¬F')
        (b and b')
    _*DR[_] :
      ∀ {r : RegularExpression} →
      {¬FL ¬F : ℙ} →
      (dr : DetReg r ¬FL ¬F true) →
      (seq-unambig :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬FL) ⊎ (c ∈ ¬F)
      ) →
      DetReg
        (r *r)
        (¬F ∩ℙ ¬FL)
        ¬F
        false

  sound¬Nullable εdr = id
  sound¬Nullable ⊥dr = &-π₂
  sound¬Nullable ＂ c ＂dr = ¬Nullable-char+ ∘g id ,&p (+-singleton char ∘g literal→char c)
  sound¬Nullable (dr ⊗DR[ FL∩F'mt ] dr') =
    ¬Nullable⊗l (sound¬Nullable dr)
  sound¬Nullable (_⊕DR[_]_ {b = false} {b' = true}
    dr disjointFsts dr') = ⊕-inl ∘g sound¬Nullable dr
  sound¬Nullable (_⊕DR[_]_ {b = true} {b' = false}
    dr disjointFsts dr') = ⊕-inr ∘g sound¬Nullable dr'
  sound¬Nullable (_⊕DR[_]_ {b = true} {b' = true}
    dr disjointFsts dr') =
    ⊕-elim
      (sound¬Nullable dr)
      (sound¬Nullable dr')
    ∘g &⊕-distL
  sound¬Nullable {b = b} (dr *DR[ _ ]) = NIL

  sound¬First εdr c c∈¬F =
    disjoint-ε-char+
    ∘g id ,&p literal→char c ,⊗ string-intro
    ∘g &-swap
  sound¬First ⊥dr c c∈¬F = &-π₂
  sound¬First ＂ c' ＂dr c c∈¬F =
    ⊕ᴰ-elim (λ c'≡c → Empty.rec (c∈¬F c'≡c))
    ∘g same-first c' c
    ∘g &-swap
  sound¬First (dr ⊗DR[ _ ] _) c c∉F =
    ∉First⊗l (sound¬Nullable dr) (sound¬First dr c c∉F)
  sound¬First (dr ⊕DR[ _ ] dr') c c∉F =
    ∉First-⊕
      (sound¬First dr c (c∉F .fst))
      (sound¬First dr' c (c∉F .snd))
  sound¬First (dr *DR[ _ ]) c c∉F =
    ∉First* (sound¬First dr c c∉F)

  sound¬FollowLast εdr c _ =
    disjoint-ε-char+
    ∘g id ,&p (char+⊗r→char+ ∘g id ,⊗ literal→char c ,⊗ id)
    ∘g &-swap
  sound¬FollowLast ⊥dr c _ = &-π₂
  sound¬FollowLast ＂ c' ＂dr c _ =
    disjoint-char-char⊗char+
    ∘g &-swap
    ∘g (literal→char c' ,⊗ startsWith→char+) ,&p literal→char c'
  sound¬FollowLast (_⊗DR[_]_ {r = r} {r' = r'} {b' = false} dr seq-unambig dr')
    c (c∉FL , c∉F' , c∉FL') =
    ∉FollowLast-⊗null _ _
      (sound¬Nullable dr)
      (λ c' →
         Sum.map
           (sound¬FollowLast dr c')
           (sound¬First dr' c')
           (seq-unambig c')
      )
      c
      (sound¬FollowLast dr c c∉FL)
      (sound¬FollowLast dr' c c∉FL')
      (sound¬First dr' c c∉F')
      (DiscreteAlphabet isFinSetAlphabet)
  sound¬FollowLast (_⊗DR[_]_ {r = r} {r' = r'} {b' = true} dr seq-unambig dr')
    c c∉FL' =
    ∉FollowLast-⊗¬null _ _ (sound¬Nullable dr) (sound¬Nullable dr')
      (λ c' →
         Sum.rec
           (λ c'∉FL → inl (sound¬FollowLast dr c' c'∉FL))
           (λ c'∉F' → inr (sound¬First dr' c' c'∉F'))
           (seq-unambig c')
      )
      c
      (sound¬FollowLast dr' c c∉FL')
  sound¬FollowLast (_⊕DR[_]_ {r = r} {r' = r'} {b = b}{b' = b'} {notBothNull = notBothNull} dr sep dr')
    c (c∉FL , c∉FL' , c∉Firsts?) =
    ∉FollowLast-⊕ _ _ c
      (sound¬FollowLast dr c c∉FL)
      (sound¬FollowLast dr' c c∉FL')
      ¬nullr'∨c∉F
      ¬nullr∨c∉F'
      (λ c' →
        Sum.map
          (sound¬First dr c')
          (sound¬First dr' c')
          (sep c')
      )
    where
    case-bool : {x y : Bool} → x or y Eq.≡ true →
      ((x Eq.≡ true) × (y Eq.≡ false)) ⊎
      (((x Eq.≡ false) × (y Eq.≡ true)) ⊎
      ((x Eq.≡ true) × (y Eq.≡ true)))
    case-bool {false} {true} _ = inr (inl (Eq.refl , Eq.refl))
    case-bool {true} {false} _ = inl (Eq.refl , Eq.refl)
    case-bool {true} {true} _ = inr (inr (Eq.refl , Eq.refl))

    elim-if : ∀ {ℓ} → {A B : Type ℓ} {x : Bool} →
      x Eq.≡ true →
      if x then A else B →
      A
    elim-if {x = true} Eq.refl the-if = the-if

    elim-if' : ∀ {ℓ} → {A B : Type ℓ} {x : Bool} →
      x Eq.≡ false →
      if x then A else B →
      B
    elim-if' {x = false} Eq.refl the-if = the-if

    ¬nullr'∨c∉F : ⟨ ¬Nullable ⟦ r' ⟧r ⟩ ⊎ ⟨ c ∉First ⟦ r ⟧r ⟩
    ¬nullr'∨c∉F =
      Sum.rec
        (λ c∉F → inr (sound¬First dr c c∉F))
        (λ c∉F' →
             Sum.rec
               (λ { (Eq.refl , Eq.refl) →
                 inr (sound¬First dr c (c∉Firsts? .fst))
               })
               (Sum.rec
                 (λ { (Eq.refl , Eq.refl) →
                   inl (sound¬Nullable dr')
                   })
                 (λ { (Eq.refl , Eq.refl) →
                   inl (sound¬Nullable dr')
                   })
                 )
               (case-bool {x = b} {y = b'} notBothNull)
        )
        (sep c)

    ¬nullr∨c∉F' : ⟨ ¬Nullable ⟦ r ⟧r ⟩ ⊎ ⟨ c ∉First ⟦ r' ⟧r ⟩
    ¬nullr∨c∉F' =
      Sum.rec
        (λ c∉F →
          Sum.rec
            (λ { (Eq.refl , Eq.refl) →
              inl (sound¬Nullable dr)
              })
            (Sum.rec
              (λ { (Eq.refl , Eq.refl) →
                inr (sound¬First dr' c (c∉Firsts? .snd))
                })
              (λ { (Eq.refl , Eq.refl) →
                inl (sound¬Nullable dr)
                }))
            (case-bool {x = b} {y = b'} notBothNull))
        (λ c∉F' →
          inr (sound¬First dr' c c∉F')
        )
        (sep c)
  sound¬FollowLast (dr *DR[ seq-unambig ]) c (c∉F , c∉FL) =
    ∉FollowLast-* _ c
      (sound¬First dr c c∉F)
      (sound¬FollowLast dr c c∉FL)
      (sound¬Nullable dr)
      (λ c' →
        Sum.map
          (sound¬FollowLast dr c')
          (sound¬First dr c')
          (seq-unambig c')
      )
      (DiscreteAlphabet isFinSetAlphabet)

  unambiguousDR εdr = unambiguousε
  unambiguousDR ⊥dr = unambiguous⊥
  unambiguousDR ＂ c ＂dr = unambiguous-literal c
  unambiguousDR (dr ⊗DR[ seq-unambig ] dr') =
    unambiguous-⊗
      (sound¬Nullable dr)
      (λ c →
        Sum.map
          (sound¬FollowLast dr c)
          (sound¬First dr' c)
          (seq-unambig c))
      (unambiguousDR dr)
      (unambiguousDR dr')
  unambiguousDR (_⊕DR[_]_ {b = b}{b' = b'}{notBothNull = notBothNull} dr sep dr') =
    unambiguous⊕
      (#→disjoint
        (λ c →
           Sum.map
             (sound¬First dr c)
             (sound¬First dr' c)
             (sep c))
        ¬null
      )
      (unambiguousDR dr)
      (unambiguousDR dr')
    where
    case-bool : {x y : Bool} → x or y Eq.≡ true →
      ((x Eq.≡ true) × (y Eq.≡ false)) ⊎
      (((x Eq.≡ false) × (y Eq.≡ true)) ⊎
      ((x Eq.≡ true) × (y Eq.≡ true)))
    case-bool {false} {true} _ = inr (inl (Eq.refl , Eq.refl))
    case-bool {true} {false} _ = inl (Eq.refl , Eq.refl)
    case-bool {true} {true} _ = inr (inr (Eq.refl , Eq.refl))

    ¬null =
      Sum.rec
        (λ { (Eq.refl , Eq.refl) → inl (sound¬Nullable dr)})
        (
        Sum.rec
          (λ { (Eq.refl , Eq.refl) → inr (sound¬Nullable dr')})
          (λ { (Eq.refl , Eq.refl) → inl (sound¬Nullable dr)})
        )
        (case-bool {x = b}{y = b'} notBothNull)
  unambiguousDR (dr *DR[ seq-unambig ]) =
    unambiguous-*
      (sound¬Nullable dr)
      (λ c →
         Sum.map
           (sound¬FollowLast dr c)
           (sound¬First dr c)
           (seq-unambig c))
      (unambiguousDR dr)
