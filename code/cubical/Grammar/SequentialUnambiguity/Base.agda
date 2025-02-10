{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Base (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Negation.Properties Alphabet
open import Grammar.LinearProduct.SplittingTrichotomy Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Grammar.SequentialUnambiguity.FollowLast Alphabet
open import Grammar.PropositionalTruncation.Base Alphabet
open import Term Alphabet

open import Grammar.Subgrammar.Base Alphabet renaming (true to trueG ; false to falseG)

open import Cubical.Foundations.Powerset.More

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    c : ⟨ Alphabet ⟩

open StrongEquivalence
open Powerset ⟨ Alphabet ⟩

sequentiallyUnambiguous :
  Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
sequentiallyUnambiguous g h =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast g ⟩ ⊎ ⟨ c ∉First h ⟩

syntax sequentiallyUnambiguous g h = g ⊛ h

module _
  (g : Grammar ℓg)
  (c : ⟨ Alphabet ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (disc : Discrete ⟨ Alphabet ⟩)
  where
  ∉FollowLast→⊛ : g ⊛ startsWith c
  ∉FollowLast→⊛ c' =
    decRec
      (λ c≡c' → inl (c∉FLg ∘g (id ,⊗ transportG (cong ＂_＂ (sym c≡c')) ,⊗ id) ,&p id))
      (λ c≢c' → inr (⊕ᴰ-elim (λ c'≡c → Empty.rec (c≢c' (sym c'≡c))) ∘g same-first' c' c))
      (disc c c')

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (seq-unambig : sequentiallyUnambiguous g h)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where
  sequentiallyUnambiguous⊗l : sequentiallyUnambiguous g (h ⊗ k)
  sequentiallyUnambiguous⊗l c =
    Sum.map (λ x → x) (∉First⊗l ¬nullh) (seq-unambig c)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (seq-unambig : sequentiallyUnambiguous g h)
  where
  sequentiallyUnambiguous& : sequentiallyUnambiguous g (h & k)
  sequentiallyUnambiguous& c =
    Sum.map (λ x → x) (∉First∘g &-π₁) (seq-unambig c)

sequentiallyUnambiguous' :
  Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
sequentiallyUnambiguous' g h =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast' g ⟩ ⊎ ⟨ c ∉First h ⟩

sequentiallyUnambiguous→sequentiallyUnambiguous' :
  sequentiallyUnambiguous g h →
  sequentiallyUnambiguous' g h
sequentiallyUnambiguous→sequentiallyUnambiguous' seq-unambig c =
  Sum.map ¬FollowLast→¬FollowLast' (λ x → x) (seq-unambig c)

seq-unambig-≅L :
  sequentiallyUnambiguous g h → g ≅ k → sequentiallyUnambiguous k h
seq-unambig-≅L seq-unambig g≅k c =
  Sum.map
    (λ c∉FLg → c∉FLg ∘g (g≅k .inv ,⊗ id) ,&p g≅k .inv)
    (λ x → x)
    (seq-unambig c)

seq-unambig-≅R :
  sequentiallyUnambiguous' g h → h ≅ k → sequentiallyUnambiguous' g k
seq-unambig-≅R seq-unambig h≅k c =
  Sum.map (λ x → x) (λ c∉Fh → c∉Fh ∘g id ,&p h≅k .inv) (seq-unambig c)

sequentiallyUnambiguous'→sequentiallyUnambiguous :
  sequentiallyUnambiguous' g h →
  ⟨ ¬Nullable g ⟩ →
  sequentiallyUnambiguous g h
sequentiallyUnambiguous'→sequentiallyUnambiguous seq-unambig' ¬nullg c =
  Sum.map (¬FollowLast'→¬FollowLast ¬nullg) (λ x → x) (seq-unambig' c)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (seq-unambig-h : sequentiallyUnambiguous g h)
  (seq-unambig-k : sequentiallyUnambiguous g k)
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

  ⊗&-distL≅ :
    (g ⊗ h) & (g ⊗ k)
    ≅
    (g & g) ⊗ (h & k)
  ⊗&-distL≅ =
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
  (seq-unambig-h : sequentiallyUnambiguous' g h)
  (seq-unambig-k : sequentiallyUnambiguous' g k)
  where
  ⊗&-distL≅' :
    (g ⊗ h) & (g ⊗ k)
    ≅
    (g & g) ⊗ (h & k)
  ⊗&-distL≅' =
    ⊗&-distL≅ g h k
      (sequentiallyUnambiguous'→sequentiallyUnambiguous seq-unambig-h ¬nullg)
      (sequentiallyUnambiguous'→sequentiallyUnambiguous seq-unambig-k ¬nullg)

seq-unambig-εL : sequentiallyUnambiguous ε g
seq-unambig-εL c = inl ((disjoint-ε-char+ ∘g id ,&p (literal→char c ,⊗ id ∘g ⊗-unit-l)) ∘g &-swap)

seq-unambig-εR : sequentiallyUnambiguous g ε
seq-unambig-εR c = inr (disjoint-ε-char+ ∘g id ,&p literal→char c ,⊗ id ∘g &-swap)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (seq-unambig : sequentiallyUnambiguous g h)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where

  ⊛→must-split : disjoint g (g ⊗ h ⊗ string)
  ⊛→must-split =
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
  (seq-unambig : sequentiallyUnambiguous g h)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where

  factor⊗3≅ :
    (g ⊗ h ⊗ k) & (g ⊗ h ⊗ l)
    ≅
    (g & g) ⊗ ((h ⊗ k) & (h ⊗ l))
  factor⊗3≅ =
    ⊗&-distL≅ g (h ⊗ k) (h ⊗ l)
      (sequentiallyUnambiguous⊗l g h k seq-unambig ¬nullh)
      (sequentiallyUnambiguous⊗l g h l seq-unambig ¬nullh)

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (l : Grammar ℓl)
  (seq-unambig : sequentiallyUnambiguous' g h)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  where
  factor⊗3≅' :
    (g ⊗ h ⊗ k) & (g ⊗ h ⊗ l)
    ≅
    (g & g) ⊗ ((h ⊗ k) & (h ⊗ l))
  factor⊗3≅' =
    factor⊗3≅ g h k l
      (sequentiallyUnambiguous'→sequentiallyUnambiguous seq-unambig ¬nullg)
      ¬nullh

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (¬nullh : ⟨ ¬Nullable h ⟩)
  (seq-unambig : g ⊛ h)
  (c : ⟨ Alphabet ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  where
  ∉FollowLast-⊗¬null : ⟨ c ∉FollowLast (g ⊗ h) ⟩
  ∉FollowLast-⊗¬null =
    ⊗⊥
    ∘g id ,⊗ c∉FLh
    ∘g ⊗&-distL≅
         g
         (h ⊗ ＂ c ＂ ⊗ string)
         h
         (sequentiallyUnambiguous⊗l g h (＂ c ＂ ⊗ string) seq-unambig ¬nullh)
         seq-unambig
         .fun
    ∘g ⊗-assoc⁻ ,&p id

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (¬nullg : ⟨ ¬Nullable g ⟩)
  (seq-unambig : g ⊛ h)
  (c : ⟨ Alphabet ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  (c∉Fh : ⟨ c ∉First h ⟩)
  (disc : Discrete ⟨ Alphabet ⟩)
  where
  ∉FollowLast-⊗null : ⟨ c ∉FollowLast (g ⊗ h) ⟩
  ∉FollowLast-⊗null =
    ⊕-elim
      (⊗⊥
      ∘g id ,⊗ c∉Fh
      ∘g ⊗&-distL≅ g (＂ c ＂ ⊗ string) h (∉FollowLast→⊛ g c c∉FLg disc) seq-unambig .fun
      ∘g ((⊗-unit-r ∘g id ,⊗ &-π₂) ,⊗ id ∘g ⊗-assoc) ,&p id)
      (⊕-elim
        (⊛→must-split g (h & char +) g⊛h+ ¬nullh+
        ∘g id ,&p id ,⊗ id ,⊗ string-intro
        ∘g &-swap
        ∘g id ,&p (⊗-unit-r ∘g id ,⊗ &-π₂))
        (∉FollowLast-⊗¬null g (h & (char +)) ¬nullg ¬nullh+ g⊛h+ c c∉FLh+
        ∘g ⊗-assoc ,&p id)
      ∘g &⊕-distL
      ∘g id ,&p (⊗⊕-distL ∘g id ,⊗ &string-split≅ .fun))
    ∘g &⊕-distR
    ∘g (⊗⊕-distL ∘g id ,⊗ (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ∘g ⊗-assoc⁻) ,&p id
    where
    g⊛h+ : g ⊛ (h & (char +))
    g⊛h+ = sequentiallyUnambiguous& g h (char +) seq-unambig

    ¬nullh+ : ⟨ ¬Nullable (h & (char +)) ⟩
    ¬nullh+ = ¬Nullable∘g &-π₂ ¬Nullable-char+

    c∉FLh+ : ⟨ c ∉FollowLast (h & (char +)) ⟩
    c∉FLh+ = ¬FollowLast∘g &-π₁ c∉FLh

module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (c : ⟨ Alphabet ⟩)
  (c∉FLg : ⟨ c ∉FollowLast g ⟩)
  (c∉FLh : ⟨ c ∉FollowLast h ⟩)
  (¬nullh∨c∉Fg : ⟨ ¬Nullable h ⟩ ⊎ ⟨ c ∉First g ⟩)
  (¬nullg∨c∉Fh : ⟨ ¬Nullable g ⟩ ⊎ ⟨ c ∉First h ⟩)
  (sep : g # h)
  where
  ∉FollowLast-⊕ : ⟨ c ∉FollowLast (g ⊕ h) ⟩
  ∉FollowLast-⊕ =
    ⊕-elim
      (⊕-elim
        c∉FLg
        (Sum.rec
          (λ ¬nullh →
            #→disjoint
              (#⊗l
                (¬Nullable∘g &-π₂ ¬Nullable-char+)
                (sym# (#∘g2 &-π₁ &-π₁ sep))
              )
              (¬Nullable⊗l ¬Nullable-&char+)
            ∘g (¬Nullable&char+≅ ¬nullh .fun ,⊗ id ∘g &-π₁) ,& &-π₂ ,& (¬Nullable→char+ (¬Nullable⊗l ¬nullh) ∘g &-π₁)
          )
          (λ c∉Fg →
            ⊕-elim
              (c∉Fg
              ∘g (⊗-unit-l ∘g &-π₂ ,⊗ id) ,&p id)
              (#→disjoint (#⊗l ¬Nullable-&char+ (#∘g &-π₁ (sym# sep))) (¬Nullable⊗l ¬Nullable-&char+))
            ∘g &⊕-distR
            ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id
          )
          ¬nullh∨c∉Fg)
      ∘g &⊕-distR)
      (⊕-elim
        (Sum.rec
          (λ ¬nullg →
            #→disjoint
              (#⊗l
                (¬Nullable∘g &-π₂ ¬Nullable-char+)
                (#∘g2 &-π₁ &-π₁ sep)
              )
              (¬Nullable⊗l ¬Nullable-&char+)
            ∘g (¬Nullable&char+≅ ¬nullg .fun ,⊗ id ∘g &-π₁) ,& &-π₂ ,& (¬Nullable→char+ (¬Nullable⊗l ¬nullg) ∘g &-π₁)
          )
          (λ c∉Fh →
            ⊕-elim
              (c∉Fh
              ∘g (⊗-unit-l ∘g &-π₂ ,⊗ id) ,&p id)
              (#→disjoint (#⊗l ¬Nullable-&char+ (#∘g &-π₁ sep)) (¬Nullable⊗l ¬Nullable-&char+))
            ∘g &⊕-distR
            ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id
          )
          ¬nullg∨c∉Fh)
        c∉FLh
      ∘g &⊕-distR)
    ∘g &⊕-distL
    ∘g ⊗⊕-distR ,&p id

-- module _
--   (g : Grammar ℓg)
--   (c : ⟨ Alphabet ⟩)
--   (c∉Fg : ⟨ c ∉First g ⟩)
--   (c∉FLg : ⟨ c ∉FollowLast g ⟩)
--   (¬nullg : ⟨ ¬Nullable g ⟩)
--   (seq-unambig : sequentiallyUnambiguous g g)
--   where

--   private
--     nonmt-* : (g *) & (char +) ≅ g ⊗ (g *)
--     nonmt-* =
--       &≅ (*≅ε⊕g⊗g* g) id≅
--       ≅∙ &⊕-distR≅
--       ≅∙ ⊕≅ (uninhabited→≅⊥ disjoint-ε-char+) id≅
--       ≅∙ ⊕≅
--         (sym≅
--           (uninhabited→≅⊥
--             (disjoint-ε-char+
--             ∘g id ,&p ¬Nullable→char+ (¬Nullable⊗l ¬nullg)
--             ∘g &-swap
--             )
--           )
--         )
--         id≅
--       ≅∙ sym≅ &string-split≅

--     -- the subgrammar of g* such that there does
--     -- not exist a parse of FollowLastG (g *) c over the
--     -- same word
--     notFL : Grammar ℓg
--     notFL = ∃subgrammar (g *) (¬G FollowLastG (g *) c)

--     open Subgrammar (∃-prop (g *) (¬G FollowLastG (g *) c))

--     nil-pf' : ε ⊢ ¬G FollowLastG (g *) c
--     nil-pf' =
--       ⇒-intro
--         (disjoint-ε-char+
--          ∘g id ,&p ((char+⊗l→char+ ∘g &-π₂ ,⊗ string-intro) ∘g &-π₁))

--     nil-pf : ε ⊢ ∥ ¬G FollowLastG (g *) c ∥
--     nil-pf = trunc ∘g nil-pf'

--     cons-pf' : g ⊗ notFL ⊢ ¬G FollowLastG (g *) c
--     cons-pf' =
--       ⇒-intro
--         (⊕-elim
--           (disjoint-ε-char+
--           ∘g &-swap
--           ∘g ¬Nullable→char+ (¬Nullable⊗l ¬nullg) ,&p (&-π₂ ∘g &-π₂)
--           )
--           ({!!}
--           ∘g {!!}
--           ∘g {!!}
--           ∘g id ,&p id ,&p nonmt-* .fun)
--         ∘g &⊕-distL
--         ∘g id ,&p (&⊕-distL ∘g (⊗-assoc⁻ ∘g nonmt-* .fun ,⊗ id) ,&p &string-split≅ .fun)
--         )

--     cons-pf : g ⊗ notFL ⊢ ∥ ¬G FollowLastG (g *) c ∥
--     cons-pf = trunc ∘g cons-pf'

--     total : g * ⊢ notFL
--     total =
--       subgrammar-ind'
--         (*Ty g)
--         (λ _ → g *)
--         (λ _ → unambiguous-prop unambiguous∥∥ (g *))
--         (λ _ →
--           ⊕ᴰ≡ _ _
--             λ {
--                nil →
--                  insert-pf
--                    (NIL ∘g lowerG ∘g lowerG)
--                    (nil-pf
--                     ∘g lowerG ∘g lowerG)
--                  ∙ cong (trueG ∘g_) (unambiguous⊤ _ _)
--              ; cons →
--                  insert-pf
--                    (CONS ∘g id ,⊗ sub-π ∘g lowerG ,⊗ lowerG)
--                    (cons-pf ∘g lowerG ,⊗ lowerG)
--                  ∙ cong (trueG ∘g_) (unambiguous⊤ _ _)
--             }
--         )
--         _

--   ∉FollowLast-* : ⟨ c ∉FollowLast (g *) ⟩
--   ∉FollowLast-* =
--     ⇒-app
--     ∘g (&-π₁ ∘g &-π₂) ,& &-π₁ ,& (&-π₂ ∘g &-π₂)
--     ∘g id ,&p ((∥∥idem unambiguous¬G .inv ∘g witness∃ _ _ ∘g total) ,&p id ∘g &-Δ)
