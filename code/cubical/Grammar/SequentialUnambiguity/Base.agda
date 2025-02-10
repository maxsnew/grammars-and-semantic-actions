{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Base (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.List
import Cubical.Data.Empty as Empty

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
