{--
-- Deterministic Regular Expressions
--
-- Roadmap is to
-- 1. Prove that the sets attached to the parameters of the DetReg type
--    actually match the first and follow sets (We are here rn)
-- 2. Build automata for these and prove them equivalent to the
--    deterministic regexes. Try to reuse the building blocks
--    from the Thompson proofs if possible
-- 3. Use these automata as a parser, and likely as a proof of unambiguity.
--    Although we might be able to prove unambiguity directly?
--}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet
open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Foundations.Powerset.More
open import Cubical.Relation.Nullary.DecidablePropositions.Powerset.Base

import Cubical.HITs.PropositionalTruncation as PT

open import Grammar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Negation.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.LinearProduct.SplittingTrichotomy Alphabet
open import Grammar.Literal.Parseable Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Grammar.PropositionalTruncation.Base Alphabet

open import Grammar.Subgrammar.Base Alphabet renaming (true to trueG ; false to falseG)

open import Term Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    c : ⟨ Alphabet ⟩

open StrongEquivalence

open Powerset ⟨ Alphabet ⟩
open PowersetOverSet (Alphabet .snd)

NullableG : Grammar ℓg → Grammar ℓg
NullableG g = ε & g

¬Nullable_ : Grammar ℓg → hProp ℓg
(¬Nullable g) .fst = uninhabited (NullableG g)
(¬Nullable g) .snd = isProp-uninhabited

¬Nullable→char+ : ⟨ ¬Nullable g ⟩ → g ⊢ char +
¬Nullable→char+ notnull =
  ⊕-elim
    (⊥-elim ∘g notnull ∘g &-swap)
    &-π₂
  ∘g &string-split≅ .fun

⊢char+→¬Nullable : g ⊢ char + → ⟨ ¬Nullable g ⟩
⊢char+→¬Nullable e =
  disjoint-ε-char+'
  ∘g id ,&p e

FollowLast'G : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLast'G g c = (g ⊗ ＂ c ＂ ⊗ string) & g

FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = ((g & char +) ⊗ ＂ c ＂ ⊗ string) & g

FollowLastG++ : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG++ g c = ((g & char +) ⊗ ＂ c ＂ ⊗ string) & (g & char +)

FollowLastG⊢FollowLast'G : FollowLastG g c ⊢ FollowLast'G g c
FollowLastG⊢FollowLast'G = (&-π₁ ,⊗ id) ,&p id

_∉FollowLast'_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast' g) .fst = uninhabited (FollowLast'G g c)
(c ∉FollowLast' g) .snd = isProp-uninhabited

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast g) .fst = uninhabited (FollowLastG g c)
(c ∉FollowLast g) .snd = isProp-uninhabited

¬FollowLast'→¬FollowLast : ⟨ c ∉FollowLast' g ⟩ → ⟨ c ∉FollowLast g ⟩
¬FollowLast'→¬FollowLast c∉FL' = c∉FL' ∘g FollowLastG⊢FollowLast'G

¬FollowLast→¬FollowLast' :
  ⟨ ¬Nullable g ⟩ → ⟨ c ∉FollowLast g ⟩ → ⟨ c ∉FollowLast' g ⟩
¬FollowLast→¬FollowLast' ¬nullg c∉FL =
  c∉FL ∘g ((id ,&p ¬Nullable→char+ ¬nullg ∘g &-Δ) ,⊗ id) ,&p id

-- It might be nice to have a version of this
-- at an arbitrary level, but I don't
-- want to refactor the powerset code rn
-- or use explicit lifts
¬FollowLast' : Grammar ℓ-zero → ℙ
¬FollowLast' g c = c ∉FollowLast' g

¬FollowLast : Grammar ℓ-zero → ℙ
¬FollowLast g c = c ∉FollowLast g

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ string) & g

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉First g) .fst = uninhabited (FirstG g c)
(c ∉First g) .snd = isProp-uninhabited

¬First : Grammar ℓ-zero → ℙ
¬First g c = c ∉First g


¬Nullable⊗l : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (g ⊗ h) ⟩
¬Nullable⊗l notnull =
  ⊢char+→¬Nullable (char+⊗l→char+ ∘g ¬Nullable→char+ notnull ,⊗ id)

¬Nullable⊗r : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (h ⊗ g) ⟩
¬Nullable⊗r notnull =
  ⊢char+→¬Nullable (char+⊗r→char+ ∘g id ,⊗ ¬Nullable→char+ notnull)

FollowLastG++≅ :
  Grammar ℓg → ⟨ Alphabet ⟩ →
  FollowLastG g c ≅ FollowLastG++ g c
FollowLastG++≅ g c =
  &≅ id≅ &string-split≅
  ≅∙ &⊕-distL≅
  ≅∙ ⊕≅
    (uninhabited→≅⊥
      (disjoint-ε-char+
      ∘g &-swap
      ∘g ¬Nullable→char+ (¬Nullable⊗l (disjoint-ε-char+ ∘g id ,&p &-π₂)) ,&p &-π₂))
    id≅
  ≅∙ ⊥⊕≅ _

∉First⊗l' : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ string) ⟩
∉First⊗l' {g = g} {c = c} ¬nullg c∉Fg =
  ⊕-elim
    (⊥⊗ ∘g (¬nullg ∘g &-swap) ,⊗ id ∘g &-π₂)
    (⊕ᴰ-elim (λ c' →
      ⊕ᴰ-elim (λ c≡c' →
        (⊥⊗ ∘g
          (c∉Fg ∘g
            (transportG
             (cong literal (sym c≡c')) ,⊗ id) ,&p id ∘g &-swap) ,⊗ id)
        ∘g &-π₂ ∘g &-π₁
      )
      ∘g &⊕ᴰ-distR≅ .fun
      ∘g id ,&
        (same-first' c c' ∘g
        (id ,&p ((id ,⊗ string-intro ∘g ⊗-assoc⁻) ∘g &-π₂ ,⊗ id)))
    )
    ∘g &⊕ᴰ-distR≅ .fun
    ∘g id ,&p ⊕ᴰ-distL .fun
    )
  ∘g &⊕-distL
  ∘g id ,&p (⊗⊕-distR ∘g (firstChar≅ .fun ,⊗ id))

∉First⊗l : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ h) ⟩
∉First⊗l {g = g} {c = c} {h = h} ¬nullg c∉Fg =
  ∉First⊗l' ¬nullg c∉Fg
  ∘g id ,&p (id ,⊗ string-intro)

sequentiallyUnambiguous' :
  Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
sequentiallyUnambiguous' g h =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast' g ⟩ ⊎ ⟨ c ∉First h ⟩

sequentiallyUnambiguous :
  Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
sequentiallyUnambiguous g h =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast g ⟩ ⊎ ⟨ c ∉First h ⟩

sequentiallyUnambiguous'→sequentiallyUnambiguous :
  sequentiallyUnambiguous' g h →
  sequentiallyUnambiguous g h
sequentiallyUnambiguous'→sequentiallyUnambiguous seq-unambig' c =
  Sum.map ¬FollowLast'→¬FollowLast (λ x → x) (seq-unambig' c)

seq-unambig'-≅L :
  sequentiallyUnambiguous' g h → g ≅ k → sequentiallyUnambiguous' k h
seq-unambig'-≅L seq-unambig g≅k c =
  Sum.map
    (λ c∉FLg → c∉FLg ∘g (g≅k .inv ,⊗ id) ,&p g≅k .inv)
    (λ x → x)
    (seq-unambig c)

seq-unambig'-≅R :
  sequentiallyUnambiguous' g h → h ≅ k → sequentiallyUnambiguous' g k
seq-unambig'-≅R seq-unambig h≅k c =
  Sum.map (λ x → x) (λ c∉Fh → c∉Fh ∘g id ,&p h≅k .inv) (seq-unambig c)

sequentiallyUnambiguous→sequentiallyUnambiguous' :
  sequentiallyUnambiguous g h →
  ⟨ ¬Nullable g ⟩ →
  sequentiallyUnambiguous' g h
sequentiallyUnambiguous→sequentiallyUnambiguous' seq-unambig ¬nullg c =
  Sum.map (¬FollowLast→¬FollowLast' ¬nullg) (λ x → x) (seq-unambig c)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓh)
  (seq-unambig-h : sequentiallyUnambiguous' g h)
  (seq-unambig-k : sequentiallyUnambiguous' g k)
  where

  private
    uninhabitedFirstPrefixG :
      firstPrefixG g h g k ⊢ ⊥
    uninhabitedFirstPrefixG =
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉Flg →
              ⊥⊗
              ∘g (c∉Flg ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((&-π₁ ∘g &-π₁) ,⊗ &-π₂) ,&p (&-π₁ ,⊗ &-π₂)
            )
            (λ c∉Fk →
              ⊗⊥
              ∘g id ,⊗ (c∉Fk ∘g &-swap)
              ∘g id ,⊗ (&-π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g &-π₂
            )
            (seq-unambig-k c)
        })))))

    uninhabitedSecondPrefixG :
      secondPrefixG g h g k ⊢ ⊥
    uninhabitedSecondPrefixG =
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉Flg →
              ⊥⊗
              ∘g (c∉Flg ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((&-π₁ ∘g &-π₁) ,⊗ &-π₂) ,&p (&-π₁ ,⊗ &-π₂)
            )
            (λ c∉Fh →
              ⊗⊥
              ∘g id ,⊗ (c∉Fh ∘g &-swap)
              ∘g id ,⊗ (&-π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g &-π₂
            )
            (seq-unambig-h c)
        })))))

  sequentiallyUnambiguous'⊗≅ :
    (g ⊗ h) & (g ⊗ k)
    ≅
    (g & g) ⊗ (h & k)
  sequentiallyUnambiguous'⊗≅ =
    ⊗&-split g h g k
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
    ≅∙ ⊥⊕≅ (g & g ⊗ h & k)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓh)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig-h : sequentiallyUnambiguous g h)
  (seq-unambig-k : sequentiallyUnambiguous g k)
  where
  sequentiallyUnambiguous⊗≅ :
    (g ⊗ h) & (g ⊗ k)
    ≅
    (g & g) ⊗ (h & k)
  sequentiallyUnambiguous⊗≅ =
    sequentiallyUnambiguous'⊗≅ g h k
      (sequentiallyUnambiguous→sequentiallyUnambiguous' seq-unambig-h ¬nullg)
      (sequentiallyUnambiguous→sequentiallyUnambiguous' seq-unambig-k ¬nullg)

-- seq-unambig-εL : sequentiallyUnambiguous' ε g
-- seq-unambig-εL c = inl ((disjoint-ε-char+ ∘g id ,&p (literal→char c ,⊗ id ∘g ⊗-unit-l)) ∘g &-swap)

-- seq-unambig-εR : sequentiallyUnambiguous' g ε
-- seq-unambig-εR c = inr (disjoint-ε-char+ ∘g id ,&p literal→char c ,⊗ id ∘g &-swap)


-- module _
--   (g : Grammar ℓg)
--   (seq-unambig : sequentiallyUnambiguous' g g)
--   where

--   sequentiallyUnambiguous'IteratedTensor : ∀ n → sequentiallyUnambiguous' g (iterated-tensor g n)
--   sequentiallyUnambiguous'IteratedTensor zero = seq-unambig-≅R seq-unambig-εR (LiftG≅ ℓg ε)
--   sequentiallyUnambiguous'IteratedTensor (suc n) = {!!}


module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (seq-unambig : sequentiallyUnambiguous' g h)
  where

  module _ (¬nullh : ⟨ ¬Nullable h ⟩) where
    disjoint-g-g⊗h⊗⊤ : disjoint g (g ⊗ h ⊗ ⊤)
    disjoint-g-g⊗h⊗⊤ =
      ⊕ᴰ-elim (λ c →
        Sum.rec
          (λ c∉FL →
            c∉FL
            ∘g &-swap
            ∘g id ,&p (id ,⊗ (id ,⊗ string-intro ∘g ⊗-assoc⁻ ∘g &-π₂ ,⊗ id))
          )
          (λ c∉Fh →
            ⊗⊥
            ∘g id ,⊗ (⊥⊗ ∘g (c∉Fh ∘g &-swap) ,⊗ id)
            ∘g &-π₂
          )
          (seq-unambig c)
      )
      ∘g &⊕ᴰ-distR≅ .fun
      ∘g id ,&p
        (⊕ᴰ-distR .fun
        ∘g id ,⊗
          (⊕ᴰ-distL .fun
          ∘g (⊥⊕≅ _ .fun
              ∘g ((¬nullh ∘g &-swap) ,⊕p id)
              ∘g firstChar≅ .fun) ,⊗ id))

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (l : Grammar ℓl)
  (seq-unambig : sequentiallyUnambiguous' g h)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where

  private
    uninhabitedFirstPrefixG :
      firstPrefixG g (h ⊗ k) g (h ⊗ l) ⊢ ⊥
    uninhabitedFirstPrefixG =
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉Flg →
              ⊥⊗
              ∘g (c∉Flg ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((&-π₁ ∘g &-π₁) ,⊗ &-π₂) ,&p (&-π₁ ,⊗ &-π₂)
            )
            (λ c∉Fh →
              ⊗⊥
              ∘g id ,⊗ (∉First⊗l ¬nullh c∉Fh ∘g &-swap)
              ∘g id ,⊗ (&-π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g &-π₂
            )
            (seq-unambig c)
        })))))

    uninhabitedSecondPrefixG :
      secondPrefixG g (h ⊗ k) g (h ⊗ l) ⊢ ⊥
    uninhabitedSecondPrefixG =
      ⊕ᴰ-elim (λ y →
      ⊕ᴰ-elim (λ z →
      ⊕ᴰ-elim (λ w →
      ⊕ᴰ-elim (λ x →
      ⊕ᴰ-elim (λ {
          ([] , notmt) → Empty.rec (notmt refl)
        ; (c ∷ v , notmt) →
          Sum.rec
            (λ c∉Flg →
              ⊥⊗
              ∘g (c∉Flg ∘g (id ,⊗ id ,⊗ string-intro) ,&p id ∘g &-swap) ,⊗ id
              ∘g ⌈⌉-⊗&-distR⁻ {w = x}
              ∘g id ,&p ⊗-assoc
              ∘g ((&-π₁ ∘g &-π₁) ,⊗ &-π₂) ,&p (&-π₁ ,⊗ &-π₂)
            )
            (λ c∉Fh →
              ⊗⊥
              ∘g id ,⊗ (∉First⊗l ¬nullh c∉Fh ∘g &-swap)
              ∘g id ,⊗ (&-π₁ ,&p (id ,⊗ string-intro ∘g ⊗-assoc⁻))
              ∘g &-π₂
            )
            (seq-unambig c)
        })))))

  sequentiallyUnambiguous'≅ :
    (g ⊗ h ⊗ k) & (g ⊗ h ⊗ l)
    ≅
    (g & g) ⊗ ((h ⊗ k) & (h ⊗ l))
  sequentiallyUnambiguous'≅ =
    ⊗&-split g (h ⊗ k) g (h ⊗ l)
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
    ≅∙ ⊥⊕≅ _

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (l : Grammar ℓl)
  (seq-unambig : sequentiallyUnambiguous g h)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where
  sequentiallyUnambiguous≅ :
    (g ⊗ h ⊗ k) & (g ⊗ h ⊗ l)
    ≅
    (g & g) ⊗ ((h ⊗ k) & (h ⊗ l))
  sequentiallyUnambiguous≅ =
    sequentiallyUnambiguous'≅ g h k l
      (sequentiallyUnambiguous→sequentiallyUnambiguous' seq-unambig ¬nullg)
      ¬nullh

disjoint¬Firsts→disjoint :
  (∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉First g ⟩ ⊎ ⟨ c ∉First h ⟩) →
  ⟨ ¬Nullable g ⟩ →
  disjoint g h
disjoint¬Firsts→disjoint disjFsts ¬nullg =
  ⊕-elim
    (¬nullg ∘g id ,&p &-π₁ ∘g &-swap)
    (⊕ᴰ-elim (λ c →
      Sum.rec
        (λ c∉Fg → c∉Fg ∘g &-swap ∘g &-π₁ ,&p id)
        (λ c∉Fh → c∉Fh ∘g &-swap ∘g &-π₂ ,&p id)
        (disjFsts c)
    )
    ∘g &⊕ᴰ-distR≅ .fun
    ∘g id ,&p ⊕ᴰ-distL .fun)
  ∘g &string-split≅ .fun

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig : sequentiallyUnambiguous g h)
  (c : ⟨ Alphabet ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  (c∉Fh : ⟨ c ∉First h ⟩)
  where
  ∉FollowLast-⊗null : ⟨ c ∉FollowLast (g ⊗ h) ⟩
  ∉FollowLast-⊗null = {!!}

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  (seq-unambig : sequentiallyUnambiguous g h)
  (c : ⟨ Alphabet ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  where
  ∉FollowLast-⊗¬null : ⟨ c ∉FollowLast (g ⊗ h) ⟩
  ∉FollowLast-⊗¬null = {!!}

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (c : ⟨ Alphabet ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  (Fg∩Fhmt : ∀ c → ⟨ c ∉First g ⟩ ⊎ ⟨ c ∉First h ⟩)
  where
  ∉FollowLast-⊕ : ⟨ c ∉FollowLast (g ⊕ h) ⟩
  ∉FollowLast-⊕ =
    ⊕-elim
      (⊕-elim
          c∉FLg
          (⊕-elim
             (disjoint-ε-char+
             ∘g &-π₂ ,&p (char+⊗r→char+ ∘g id ,⊗ (literal→char c ,⊗ id))
             ∘g &-swap
             )
             {!!}
           ∘g &⊕-distL
           ∘g id ,&p &string-split≅ .fun)
      ∘g &⊕-distR)
      (⊕-elim
          {!!}
          c∉FLh
      ∘g &⊕-distR)
    ∘g &⊕-distL
    ∘g (⊗⊕-distR ∘g &⊕-distR ,⊗ id) ,&p id


module _
  (g : Grammar ℓg)
  (c : ⟨ Alphabet ⟩)
  (c∉Fg : ⟨ c ∉First g ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig : sequentiallyUnambiguous g g)
  where

  private
    nonmt-* : (g *) & (char +) ≅ g ⊗ (g *)
    nonmt-* =
      &≅ (*≅ε⊕g⊗g* g) id≅
      ≅∙ &⊕-distR≅
      ≅∙ ⊕≅ (uninhabited→≅⊥ disjoint-ε-char+) id≅
      ≅∙ ⊕≅
        (sym≅
          (uninhabited→≅⊥
            (disjoint-ε-char+
            ∘g id ,&p ¬Nullable→char+ (¬Nullable⊗l ¬nullg)
            ∘g &-swap
            )
          )
        )
        id≅
      ≅∙ sym≅ &string-split≅

    -- the subgrammar of g* such that there does
    -- not exist a parse of FollowLastG (g *) c over the
    -- same word
    notFL : Grammar ℓg
    notFL = ∃subgrammar (g *) (¬G FollowLastG (g *) c)

    open Subgrammar (∃-prop (g *) (¬G FollowLastG (g *) c))

    nil-pf' : ε ⊢ ¬G FollowLastG (g *) c
    nil-pf' =
      ⇒-intro
        (disjoint-ε-char+
         ∘g id ,&p ((char+⊗l→char+ ∘g &-π₂ ,⊗ string-intro) ∘g &-π₁))

    nil-pf : ε ⊢ ∥ ¬G FollowLastG (g *) c ∥
    nil-pf = trunc ∘g nil-pf'

    cons-pf' : g ⊗ notFL ⊢ ¬G FollowLastG (g *) c
    cons-pf' =
      ⇒-intro
        (⊕-elim
          (disjoint-ε-char+
          ∘g &-swap
          ∘g ¬Nullable→char+ (¬Nullable⊗l ¬nullg) ,&p (&-π₂ ∘g &-π₂)
          )
          ({!!}
          ∘g {!!}
          ∘g {!!}
          ∘g id ,&p id ,&p nonmt-* .fun)
        ∘g &⊕-distL
        ∘g id ,&p (&⊕-distL ∘g (⊗-assoc⁻ ∘g nonmt-* .fun ,⊗ id) ,&p &string-split≅ .fun)
        )

    cons-pf : g ⊗ notFL ⊢ ∥ ¬G FollowLastG (g *) c ∥
    cons-pf = trunc ∘g cons-pf'

    total : g * ⊢ notFL
    total =
      subgrammar-ind'
        (*Ty g)
        (λ _ → g *)
        (λ _ → unambiguous-prop unambiguous∥∥ (g *))
        (λ _ →
          ⊕ᴰ≡ _ _
            λ {
               nil →
                 insert-pf
                   (NIL ∘g lowerG ∘g lowerG)
                   (nil-pf
                    ∘g lowerG ∘g lowerG)
                 ∙ cong (trueG ∘g_) (unambiguous⊤ _ _)
             ; cons →
                 insert-pf
                   (CONS ∘g id ,⊗ sub-π ∘g lowerG ,⊗ lowerG)
                   (cons-pf ∘g lowerG ,⊗ lowerG)
                 ∙ cong (trueG ∘g_) (unambiguous⊤ _ _)
            }
        )
        _

  ∉FollowLast-* : ⟨ c ∉FollowLast (g *) ⟩
  ∉FollowLast-* =
    ⇒-app
    ∘g (&-π₁ ∘g &-π₂) ,& &-π₁ ,& (&-π₂ ∘g &-π₂)
    ∘g id ,&p ((∥∥idem unambiguous¬G .inv ∘g witness∃ _ _ ∘g total) ,&p id ∘g &-Δ)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  data DetReg : RegularExpression → ℙ → ℙ → Bool → Type (ℓ-suc ℓ-zero)

  sound¬Nullable :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    if b then
    ⟨ ¬Nullable ⟦ r ⟧r ⟩ else
    (⟨ ¬Nullable ⟦ r ⟧r ⟩ → Empty.⊥)

  decidable¬Nullable :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    Dec ⟨ ¬Nullable ⟦ r ⟧r ⟩

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
      (FL∩F'mt :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬FL) ⊎ (c ∈ ¬F')
      ) →
      (dr' : DetReg r' ¬FL' ¬F' b') →
      DetReg
        (r ⊗r r')
        (if b' then ¬FL' else ¬FL ∩ℙ ¬F' ∩ℙ ¬FL') -- maybe wrong
        ¬F
        true
    _⊕DR[_]_ :
      ∀ {r r' : RegularExpression} →
      {¬FL ¬FL' ¬F ¬F' : ℙ} →
      {b b' : Bool} →
      {notBothNull : b or b' Eq.≡ true} →
      (dr : DetReg r ¬FL ¬F b) →
      (F∩F'mt :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬F) ⊎ (c ∈ ¬F')
      ) →
      (dr' : DetReg r' ¬FL' ¬F' b') →
      DetReg
        (r ⊕r r')
        (¬FL ∩ℙ ¬FL')
        (¬F ∩ℙ ¬F')
        (b and b')
    _*DR[_] :
      ∀ {r : RegularExpression} →
      {¬FL ¬F : ℙ} →
      (dr : DetReg r ¬FL ¬F true) →
      (F∩FLmt :
        ∀ (c : ⟨ Alphabet ⟩) →
          (c ∈ ¬FL) ⊎ (c ∈ ¬F)
      ) →
      DetReg
        (r *r)
        (¬F ∩ℙ ¬FL)
        ¬F
        false

  record ¬NullablePf (g : Grammar ℓ-zero) : Type ℓ-zero where
    field
      ¬nullpf : ⟨ ¬Nullable g ⟩

  record ¬¬NullablePf (g : Grammar ℓ-zero) : Type ℓ-zero where
    field
      ¬¬nullpf : ⟨ ¬Nullable g ⟩ → Empty.⊥

  open ¬NullablePf {{...}}
  open ¬¬NullablePf {{...}}

  instance
    ¬Nullable⊥ : ¬NullablePf ⊥
    ¬Nullable⊥ .¬nullpf = &-π₂

    ¬NullableLit : ∀ {c} → ¬NullablePf (＂ c ＂)
    ¬NullableLit {c} .¬nullpf = disjoint-ε-literal c

  instance
    ¬¬Nullableε : ¬¬NullablePf ε
    ¬¬Nullableε .¬¬nullpf e = get⊥ ((e ∘g &-Δ) _ ε-intro)

    ¬¬Nullable* : {g : Grammar ℓ-zero} → ¬¬NullablePf (g *)
    ¬¬Nullable* .¬¬nullpf e =
      get⊥ ((e ∘g id ,&p NIL ∘g &-Δ) _ ε-intro)

  sound¬Nullable εdr = ¬¬nullpf
  sound¬Nullable ⊥dr = ¬nullpf
  sound¬Nullable ＂ c ＂dr = ¬nullpf
  sound¬Nullable (dr ⊗DR[ FL∩F'mt ] dr') =
    ¬Nullable⊗l (sound¬Nullable dr)
  sound¬Nullable (_⊕DR[_]_ {b = false} {b' = true}
    dr disjointFsts dr') e =
    sound¬Nullable dr (e ∘g id ,&p ⊕-inl)
  sound¬Nullable (_⊕DR[_]_ {b = true} {b' = false}
    dr disjointFsts dr') e =
    sound¬Nullable dr' (e ∘g id ,&p ⊕-inr)
  sound¬Nullable (_⊕DR[_]_ {b = true} {b' = true}
    dr disjointFsts dr') =
    ⊕-elim
      (sound¬Nullable dr)
      (sound¬Nullable dr')
    ∘g &⊕-distL
  sound¬Nullable {b = b} (dr *DR[ _ ]) = ¬¬nullpf

  decidable¬Nullable {b = false} r = no (sound¬Nullable r)
  decidable¬Nullable {b = true} r = yes (sound¬Nullable r)

  sound¬First εdr c c∈¬F =
    disjoint-ε-char+
    ∘g id ,&p literal→char c ,⊗ string-intro
    ∘g &-swap
  sound¬First ⊥dr c c∈¬F = &-π₂
  sound¬First ＂ c' ＂dr c c∈¬F =
    ⊕ᴰ-elim (λ c'≡c → Empty.rec (c∈¬F c'≡c))
    ∘g same-first c' c
    ∘g &-swap
  sound¬First (dr ⊗DR[ FL∩F'mt ] dr₁) c c∈¬F =
    ∉First⊗l (sound¬Nullable dr) (sound¬First dr c c∈¬F)
  sound¬First (dr ⊕DR[ _ ] dr') c c∈¬F =
    ⊕-elim
      (sound¬First dr c (c∈¬F .fst))
      (sound¬First dr' c (c∈¬F .snd))
    ∘g &⊕-distL
  sound¬First (dr *DR[ _ ]) c c∈¬F =
    ⊕-elim
      (disjoint-ε-char+
       ∘g &-swap
       ∘g (literal→char c ,⊗ id) ,&p id)
      (∉First⊗l (sound¬Nullable dr) (sound¬First dr c c∈¬F))
    ∘g &⊕-distL
    ∘g id ,&p *≅ε⊕g⊗g* _ .fun

  sound¬FollowLast εdr c _ =
    disjoint-ε-char+
    ∘g id ,&p (char+⊗r→char+ ∘g id ,⊗ literal→char c ,⊗ id)
    ∘g &-swap
  sound¬FollowLast ⊥dr c _ = &-π₂
  sound¬FollowLast ＂ c' ＂dr c _ =
    disjoint-char-char⊗char+
    ∘g &-swap
    ∘g ((literal→char c' ∘g &-π₁) ,⊗ literal→char c ,⊗ id) ,&p literal→char c'
  sound¬FollowLast (_⊗DR[_]_ {r = r} {r' = r'} {b' = false} dr FL∩F'mt dr')
    c (c∉FL , c∉F' , c∉FL') =
    ∉FollowLast-⊗null _ _ (sound¬Nullable dr)
      (λ c' →
         Sum.rec
           (λ c'∉FL → inl (sound¬FollowLast dr c' c'∉FL))
           (λ c'∉F' → inr (sound¬First dr' c' c'∉F'))
           (FL∩F'mt c')
      )
      c
      (sound¬FollowLast dr c c∉FL)
      (sound¬FollowLast dr' c c∉FL')
      (sound¬First dr' c c∉F')
    -- ⊕-elim
    --   ({!∉FollowLast⊗!}
    --   ∘g ((⊗-unit-r ∘g id ,⊗ &-π₂) ,⊗ id) ,&p id)
    --   {!!}
    -- ∘g &⊕-distR≅ .fun
    -- ∘g (⊗⊕-distR ∘g ((⊗⊕-distL ∘g id ,⊗ &string-split≅ .fun) ∘g &-π₁) ,⊗ id) ,&p id
    
    -- ∘g &⊕-distR≅ .fun
    -- ∘g (⊗⊕-distR ∘g (⊗⊕-distL ∘g id ,⊗ &string-split≅ .fun) ,⊗ id) ,&p (⊗⊕-distL ∘g (id ,⊗ &string-split≅ .fun))
    -- ⊕-elim
    --   (⊕-elim
    --     (sound¬FollowLast dr c c∈¬FL
    --     ∘g ((⊗-unit-r ∘g id ,⊗ &-π₂ ) ,⊗ id) ,&p (⊗-unit-r ∘g id ,⊗ &-π₂))
    --     (⊗⊥
    --     ∘g id ,⊗ (sound¬First dr' c c∈¬F' ∘g (id ,&p &-π₁))
    --     ∘g sequentiallyUnambiguous'⊗≅ ⟦ r ⟧r (＂ c ＂ ⊗ string) (⟦ r' ⟧r & char +)
    --         (λ c' →
    --           decRec
    --             (λ c≡c' →
    --               inl (subst (λ z → ⟨ z ∉FollowLast ⟦ r ⟧r ⟩) c≡c' (sound¬FollowLast dr c c∈¬FL))
    --             )
    --             (λ c≢c' →
    --               inr
    --                 (⊕ᴰ-elim (λ c'≡c → Empty.rec (c≢c' (sym c'≡c))) ∘g same-first' c' c)
    --             )
    --             (DiscreteAlphabet isFinSetAlphabet c c')
    --         )
    --         (λ c' →
    --           Sum.rec
    --             (λ c'∈¬FL → inl (sound¬FollowLast dr c' c'∈¬FL))
    --             (λ c'∈¬F' → inr (sound¬First dr' c' c'∈¬F' ∘g id ,&p &-π₁))
    --             (FL∩F'mt c')
    --         )
    --         .fun
    --     ∘g ((⊗-unit-r ∘g id ,⊗ &-π₂) ,⊗ id) ,&p id
    --     )
    --   ∘g &⊕-distL≅ .fun)
    --   (⊕-elim
    --     (disjoint-g-g⊗h⊗⊤ ⟦ r ⟧r (⟦ r' ⟧r & (char +))
    --       (λ c' →
    --         Sum.rec
    --           (λ c'∈¬FL → inl (sound¬FollowLast dr c' c'∈¬FL))
    --           (λ c'∈¬F' → inr (sound¬First dr' c' c'∈¬F' ∘g id ,&p &-π₁))
    --           (FL∩F'mt c')
    --       )
    --       (disjoint-ε-char+ ∘g id ,&p &-π₂)
    --     ∘g &-swap
    --     ∘g (⊗-assoc⁻ ∘g id ,⊗ ⊤-intro) ,&p (⊗-unit-r ∘g id ,⊗ &-π₂))
    --     (⊗⊥
    --     ∘g id ,⊗ (sound¬FollowLast dr' c c∈¬FL' ∘g ((&-π₁ ,⊗ id) ,&p (&-π₁ ∘g ⊗-unit-r)))
    --     ∘g sequentiallyUnambiguous'≅
    --         ⟦ r ⟧r
    --         (⟦ r' ⟧r & char +)
    --         (＂ c ＂ ⊗ string)
    --         ε
    --         (λ c' →
    --           Sum.rec
    --             (λ c'∈¬FL → inl (sound¬FollowLast dr c' c'∈¬FL))
    --             (λ c'∈¬F' → inr (sound¬First dr' c' c'∈¬F' ∘g id ,&p &-π₁))
    --             (FL∩F'mt c')
    --         )
    --         (disjoint-ε-char+ ∘g id ,&p &-π₂)
    --         .fun
    --     ∘g ⊗-assoc⁻ ,&p (⊗-assoc⁻ ∘g ⊗-unit-r⁻)
    --     )
    --   ∘g &⊕-distL≅ .fun)
    -- ∘g &⊕-distR≅ .fun
    -- ∘g (⊗⊕-distR ∘g (⊗⊕-distL ∘g id ,⊗ &string-split≅ .fun) ,⊗ id) ,&p (⊗⊕-distL ∘g (id ,⊗ &string-split≅ .fun))
  sound¬FollowLast (_⊗DR[_]_ {r = r} {r' = r'} {b' = true} dr FL∩F'mt dr')
    c c∉FL' =
    ∉FollowLast-⊗¬null _ _ (sound¬Nullable dr) (sound¬Nullable dr')
      (λ c' →
         Sum.rec
           (λ c'∉FL → inl (sound¬FollowLast dr c' c'∉FL))
           (λ c'∉F' → inr (sound¬First dr' c' c'∉F'))
           (FL∩F'mt c')
      )
      c
      (sound¬FollowLast dr' c c∉FL')
    -- ⊗⊥
    -- ∘g id ,⊗
    --   (sound¬FollowLast dr' c c∈¬FL'
    --    ∘g id ,&p ⊗-unit-r
    --    ∘g &-swap)
    -- ∘g sequentiallyUnambiguous'≅
    --       ⟦ r ⟧r ⟦ r' ⟧r ε (＂ c ＂ ⊗ string)
    --       (λ c →
    --         Sum.map
    --           (sound¬FollowLast dr c)
    --           (sound¬First dr' c)
    --           (FL∩F'mt c)
    --       )
    --       (sound¬Nullable dr')
    --       .fun
    -- ∘g (⊗-assoc⁻ ∘g ⊗-unit-r⁻) ,&p ⊗-assoc⁻
    -- ∘g &-swap
    -- where
    -- c∉Flr' = sound¬FollowLast dr' c c∈¬FL'
  sound¬FollowLast (dr ⊕DR[ F∩F'mt ] dr') c (c∉FL , c∉FL') =
    ∉FollowLast-⊕ _ _ c
      (sound¬FollowLast dr c c∉FL)
      (sound¬FollowLast dr' c c∉FL')
      (λ c' →
        Sum.map
          (λ c'∉F → sound¬First dr c' c'∉F)
          (λ c'∉F' → sound¬First dr' c' c'∉F')
          (F∩F'mt c')
      )
  -- sound¬FollowLast (_⊕DR[_]_ {b = false} {b' = true}
  --   dr F∩F'mt dr') c (c∈¬FL , c∈¬FL') =
  --   {!!}
  -- sound¬FollowLast (_⊕DR[_]_ {b = true} {b' = false}
  --   dr F∩F'mt dr') c (c∈¬FL , c∈¬FL') =
  --   {!!}
  -- sound¬FollowLast (_⊕DR[_]_ {b = true} {b' = true}
  --   dr F∩F'mt dr') c (c∈¬FL , c∈¬FL') =
  --   {!!}
    -- ⊕-elim
    --   (⊕-elim
    --     (sound¬FollowLast dr c c∈¬FL)
    --     (⊕-elim
    --       (disjoint-ε-char+ ∘g id ,&p (¬Nullable→char+ (sound¬Nullable dr) ∘g &-π₂) ∘g &-swap)
    --       (⊕ᴰ-elim (λ c' →
    --         Sum.rec
    --           (λ c'∈¬F → sound¬First dr c' c'∈¬F ∘g &-π₂ ,& (&-π₂ ∘g &-π₁))
    --           (λ c'∈¬F' → ∉First⊗l (sound¬Nullable dr') (sound¬First dr' c' c'∈¬F') ∘g &-π₂ ,& (&-π₁ ∘g &-π₁))
    --           (F∩F'mt c')
    --       ))
    --     ∘g firstChar≅ .fun )
    --   )
    --   (⊕-elim
    --     (⊕-elim
    --       (disjoint-ε-char+ ∘g id ,&p (¬Nullable→char+ (sound¬Nullable dr') ∘g &-π₂) ∘g &-swap)
    --       (⊕ᴰ-elim (λ c' →
    --         Sum.rec
    --           (λ c'∈¬F → ∉First⊗l (sound¬Nullable dr) (sound¬First dr c' c'∈¬F) ∘g &-π₂ ,& (&-π₁ ∘g &-π₁))
    --           (λ c'∈¬F' → sound¬First dr' c' c'∈¬F' ∘g &-π₂ ,& (&-π₂ ∘g &-π₁))
    --           (F∩F'mt c')))
    --     ∘g firstChar≅ .fun)
    --     (sound¬FollowLast dr' c c∈¬FL')
    --   )
    -- ∘g (&⊕-distR ,⊕p &⊕-distR)
    -- ∘g &⊕-distL
    -- ∘g ⊗⊕-distR ,&p id
  sound¬FollowLast (dr *DR[ F∩FLmt ]) c (c∉F , c∉FL) =
    ∉FollowLast-* _ c
      (sound¬First dr c c∉F)
      (sound¬FollowLast dr c c∉FL)
      (sound¬Nullable dr)
      (λ c' →
        Sum.map
          (λ c'∉FL → sound¬FollowLast dr c' c'∉FL)
          (λ c'∉F → sound¬First dr c' c'∉F)
          (F∩FLmt c')
      )
    -- ⊕-elim
    --   (⊕-elim
    --     (disjoint-ε-char+
    --     ∘g &-swap
    --     ∘g (literal→char c ,⊗ id) ,&p id
    --     ∘g ⊗-unit-l ,&p id
    --     )
    --     (¬Nullable⊗l (¬Nullable⊗l (sound¬Nullable dr))
    --     ∘g &-swap)
    --   )
    --   (⊕-elim
    --     (∉First⊗l (sound¬Nullable dr) (sound¬First dr c c∈¬F)
    --     ∘g ⊗-unit-l ,&p id
    --     )
    --     {!!}
    --   )
    -- ∘g (&⊕-distR ,⊕p &⊕-distR)
    -- ∘g &⊕-distL
    -- ∘g (⊗⊕-distR ∘g *≅ε⊕g⊗g* ⟦ r ⟧r .fun ,⊗ id) ,&p (*≅ε⊕g⊗g* ⟦ r ⟧r .fun)

  unambiguousDR εdr = unambiguousε
  unambiguousDR ⊥dr = unambiguous⊥
  unambiguousDR ＂ c ＂dr = unambiguous-literal c
  unambiguousDR (dr ⊗DR[ FL∩F'mt ] dr') = {!!}
    -- due to sequential uambiguity, can
    -- show that its unambiguous by
    -- (r ⊗ r') & (r ⊗ r')
    -- ≅ (r & r) ⊗ (r' & r')
    -- ≅ r ⊗ r'
  unambiguousDR (dr ⊕DR[ F∩F'mt ] dr') = {!!}
    -- can prove that r and r' are disjoint, and thus
    -- have an unambiguous sum
  unambiguousDR (dr *DR[ _ ]) = {!!}

  -- unambiguousDR εDR = unambiguousε
  -- unambiguousDR ⊥DR = unambiguous⊥
  -- unambiguousDR (literalDR c) = unambiguous-literal c
  -- unambiguousDR (r ⊗DR-null[ x ] r') = {!!}
  -- unambiguousDR (r ⊗DR-notnull[ x ] r') = {!!}
  -- unambiguousDR (r ⊕DR-ft[ x ] r') = {!!}
  -- unambiguousDR (r ⊕DR-tf[ x ] r') = {!!}
  -- unambiguousDR (r ⊕DR-ff[ x ] r') = {!!}
  -- unambiguousDR (r *DR) = {!!}
