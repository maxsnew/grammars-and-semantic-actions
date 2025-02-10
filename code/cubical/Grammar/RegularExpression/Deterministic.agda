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

open import Grammar.SequentialUnambiguity Alphabet
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


module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  data DetReg : RegularExpression → ℙ → ℙ → Bool → Type (ℓ-suc ℓ-zero)

  sound¬Nullable :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    {b : Bool} →
    (dr : DetReg r ¬FL ¬F b) →
    if b then
    ⟨ ¬Nullable ⟦ r ⟧r ⟩ else
    -- (⟨ ¬Nullable ⟦ r ⟧r ⟩ → Empty.⊥)
    ε ⊢ ⟦ r ⟧r

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

  decidable¬Nullable {b = false} r =
    no λ x → get⊥ ((x ∘g id ,&p sound¬Nullable r ∘g &-Δ) [] ε-intro)
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
  sound¬FollowLast ＂ c' ＂dr c _ = {!!}
    -- disjoint-char-char⊗char+
    -- ∘g &-swap
    -- ∘g ((literal→char c' ∘g &-π₁) ,⊗ literal→char c ,⊗ id) ,&p literal→char c'
  sound¬FollowLast (_⊗DR[_]_ {r = r} {r' = r'} {b' = false} dr FL∩F'mt dr')
    c (c∉FL , c∉F' , c∉FL') =
    {!!}
    -- ∉FollowLast-⊗null _ _ (sound¬Nullable dr)
    --   (λ c' →
    --      Sum.rec
    --        (λ c'∉FL → inl (sound¬FollowLast dr c' c'∉FL))
    --        (λ c'∉F' → inr (sound¬First dr' c' c'∉F'))
    --        (FL∩F'mt c')
    --   )
    --   c
    --   (sound¬FollowLast dr c c∉FL)
    --   (sound¬FollowLast dr' c c∉FL')
    --   (sound¬First dr' c c∉F')
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
  sound¬FollowLast (_⊕DR[_]_ {r = r} {r' = r'} {b = b}{b' = b'} {notBothNull = notBothNull} dr F∩F'mt dr') c (c∉FL , c∉FL') =
    ∉FollowLast-⊕ _ _ c
      (sound¬FollowLast dr c c∉FL)
      (sound¬FollowLast dr' c c∉FL')
      ¬nullr'∨c∉F
      ¬nullr∨c∉F'
      (λ c' →
        Sum.map
          (sound¬First dr c')
          (sound¬First dr' c')
          (F∩F'mt c')
      )
    where
    case-bool : {x y : Bool} → x or y Eq.≡ true →
      ((x Eq.≡ true) × (y Eq.≡ false)) ⊎
      (((x Eq.≡ false) × (y Eq.≡ true)) ⊎
      ((x Eq.≡ true) × (y Eq.≡ true)))
    case-bool {false} {true} _ = inr (inl (Eq.refl , Eq.refl))
    case-bool {true} {false} _ = inl (Eq.refl , Eq.refl)
    case-bool {true} {true} _ = inr (inr (Eq.refl , Eq.refl))

    elim-if : ∀ {ℓ} → {A B : Type ℓ} {b : Bool} →
      b Eq.≡ true →
      if b then A else B →
      A
    elim-if {b = true} Eq.refl the-if = the-if

    elim-if' : ∀ {ℓ} → {A B : Type ℓ} {b : Bool} →
      b Eq.≡ false →
      if b then A else B →
      B
    elim-if' {b = false} Eq.refl the-if = the-if

    ¬nullr'∨c∉F : ⟨ ¬Nullable ⟦ r' ⟧r ⟩ ⊎ ⟨ c ∉First ⟦ r ⟧r ⟩
    ¬nullr'∨c∉F =
      {!!}
      -- Sum.rec
      --   (λ rnotnull∧r'null → inl (elim-if (rnotnull∧r'null .fst) (sound¬Nullable dr)))
      --   (Sum.rec
      --     (λ rnull∧r'notnull → inr (sound¬FollowLast dr c c∉FL ∘g (elim-if' (rnull∧r'notnull .fst) (sound¬Nullable dr) ,⊗ id ∘g ⊗-unit-l⁻) ,&p id))
      --     (λ rnotnull∧r'notnull → inl (elim-if (rnotnull∧r'notnull .fst) (sound¬Nullable dr)))
      --   )
      --   (case-bool notBothNull)

    ¬nullr∨c∉F' : ⟨ ¬Nullable ⟦ r ⟧r ⟩ ⊎ ⟨ c ∉First ⟦ r' ⟧r ⟩
    ¬nullr∨c∉F' = {!!}

    -- ∉FollowLast-⊕ _ _ c
    --   (sound¬FollowLast dr c c∉FL)
    --   (sound¬FollowLast dr' c c∉FL')
    --   (λ c' →
    --     Sum.map
    --       (λ c'∉F → sound¬First dr c' c'∉F)
    --       (λ c'∉F' → sound¬First dr' c' c'∉F')
    --       (F∩F'mt c')
    --   )
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
    {!!}
    -- ∉FollowLast-* _ c
    --   (sound¬First dr c c∉F)
    --   (sound¬FollowLast dr c c∉FL)
    --   (sound¬Nullable dr)
    --   (λ c' →
    --     Sum.map
    --       (λ c'∉FL → sound¬FollowLast dr c' c'∉FL)
    --       (λ c'∉F → sound¬First dr c' c'∉F)
    --       (F∩FLmt c')
    --   )
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

