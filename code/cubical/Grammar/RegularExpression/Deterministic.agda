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

open import Cubical.Functions.Logic renaming (⊥ to ⊥P)

open import Cubical.Data.FinSet
open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Sigma
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
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.Literal.Parseable Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet

open import Term Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh
    c : ⟨ Alphabet ⟩

open StrongEquivalence

open Powerset ⟨ Alphabet ⟩
open PowersetOverSet (Alphabet .snd)

-- TODO migrate over decidable stuff to ordinary powersets
-- the cubical library absolutely sucks for this sort of thing
-- open DecidablePowerset ⟨ Alphabet ⟩ hiding (∅ℙ ; _∩ℙ_ ; _∪ℙ_ ; ¬ℙ)

FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = (g ⊗ ＂ c ＂ ⊗ string) & g

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast g) .fst = uninhabited (FollowLastG g c)
(c ∉FollowLast g) .snd = isProp-uninhabited

-- It might be nice to have a version of this
-- at an arbitrary level, but I don't
-- want to refactor the powerset code rn
¬FollowLast : Grammar ℓ-zero → ℙ
¬FollowLast g c = c ∉FollowLast g

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ string) & g

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉First g) .fst = uninhabited (FirstG g c)
(c ∉First g) .snd = isProp-uninhabited

¬First : Grammar ℓ-zero → ℙ
¬First g c = c ∉First g

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

¬Nullable⊗l : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (g ⊗ h) ⟩
¬Nullable⊗l notnull =
  ⊢char+→¬Nullable (char+⊗l→char+ ∘g ¬Nullable→char+ notnull ,⊗ id)

¬Nullable⊗r : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (h ⊗ g) ⟩
¬Nullable⊗r notnull =
  ⊢char+→¬Nullable (char+⊗r→char+ ∘g id ,⊗ ¬Nullable→char+ notnull)

∉First⊗l' : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ string) ⟩
∉First⊗l' {g = g} {c = c} ¬nullg c∉Fg =
  {!!}

∉First⊗l : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ h) ⟩
∉First⊗l {g = g} {c = c} {h = h} ¬nullg c∉Fg =
  ∉First⊗l' ¬nullg c∉Fg
  ∘g id ,&p (id ,⊗ string-intro)

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
  _*DR :
    ∀ {r : RegularExpression} →
    {¬FL ¬F : ℙ} →
    (dr : DetReg r ¬FL ¬F true) →
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
sound¬Nullable {b = b} (dr *DR) = ¬¬nullpf

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
sound¬First (dr *DR) c c∈¬F =
  ⊕-elim
    (disjoint-ε-char+
     ∘g &-swap
     ∘g (literal→char c ,⊗ id) ,&p id)
    (∉First⊗l (sound¬Nullable dr) (sound¬First dr c c∈¬F))
  ∘g &⊕-distL
  ∘g id ,&p *≅ε⊕g⊗g* _ .fun

sound¬FollowLast εdr c _ =
  disjoint-ε-char+
  ∘g &-swap
  ∘g (literal→char c ,⊗ id ∘g ⊗-unit-l) ,&p id
sound¬FollowLast ⊥dr c _ = &-π₂
sound¬FollowLast ＂ c' ＂dr c _ =
  disjoint-char-char⊗char+
  ∘g &-swap
  ∘g (literal→char c' ,⊗ literal→char c ,⊗ id) ,&p literal→char c'
sound¬FollowLast (_⊗DR[_]_ {b' = false} dr FL∩F'mt dr')
  c (c∈¬FL , c∈¬F' , c∈¬FL') =
  {!!}
sound¬FollowLast (_⊗DR[_]_ {b' = true} dr FL∩F'mt dr')
  c c∈¬FL' =
  {!!}
sound¬FollowLast (dr ⊕DR[ F∩F'mt ] dr') c (c∈¬FL , c∈¬FL') =
  {!!}
sound¬FollowLast (dr *DR) c (c∈¬F , c∈¬FL) =
  {!!}

unambiguousDR dr = ?

-- -- unambiguousDR εDR = unambiguousε
-- -- unambiguousDR ⊥DR = unambiguous⊥
-- -- unambiguousDR (literalDR c) = unambiguous-literal c
-- -- unambiguousDR (r ⊗DR-null[ x ] r') = {!!}
-- -- unambiguousDR (r ⊗DR-notnull[ x ] r') = {!!}
-- -- unambiguousDR (r ⊕DR-ft[ x ] r') = {!!}
-- -- unambiguousDR (r ⊕DR-tf[ x ] r') = {!!}
-- -- unambiguousDR (r ⊕DR-ff[ x ] r') = {!!}
-- -- unambiguousDR (r *DR) = {!!}
