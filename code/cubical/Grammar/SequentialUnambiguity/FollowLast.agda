open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.FollowLast (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Term Alphabet

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


FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = (g ⊗ startsWith c) & g

FollowLastG+ : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG+ g c = (g ⊗ startsWith c) & (g & char +)

-- This is the version of FollowLast defined by Bruggemann-Klein and Wood, and
-- further used in Krishnaswami and Yallop
FollowLastG' : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG' g c = ((g & char +) ⊗ startsWith c) & g

FollowLastG'+ : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG'+ g c = ((g & char +) ⊗ startsWith c) & (g & char +)

FollowLastG'⊢FollowLastG : FollowLastG' g c ⊢ FollowLastG g c
FollowLastG'⊢FollowLastG = (&-π₁ ,⊗ id) ,&p id

_∉FollowLast'_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast' g) .fst = uninhabited (FollowLastG' g c)
(c ∉FollowLast' g) .snd = isProp-uninhabited

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast g) .fst = uninhabited (FollowLastG g c)
(c ∉FollowLast g) .snd = isProp-uninhabited

¬FollowLast→¬FollowLast' : ⟨ c ∉FollowLast g ⟩ → ⟨ c ∉FollowLast' g ⟩
¬FollowLast→¬FollowLast' c∉FL' = c∉FL' ∘g FollowLastG'⊢FollowLastG

¬FollowLast'→¬FollowLast :
  ⟨ ¬Nullable g ⟩ → ⟨ c ∉FollowLast' g ⟩ → ⟨ c ∉FollowLast g ⟩
¬FollowLast'→¬FollowLast ¬nullg c∉FL =
  c∉FL ∘g ((id ,&p ¬Nullable→char+ ¬nullg ∘g &-Δ) ,⊗ id) ,&p id

-- It might be nice to have a version of this
-- at an arbitrary level, but I don't
-- want to refactor the powerset code rn
-- or use explicit lifts
¬FollowLast' : Grammar ℓ-zero → ℙ
¬FollowLast' g c = c ∉FollowLast' g

¬FollowLast : Grammar ℓ-zero → ℙ
¬FollowLast g c = c ∉FollowLast g

FollowLastG+≅ :
  Grammar ℓg → ⟨ Alphabet ⟩ →
  FollowLastG g c ≅ FollowLastG+ g c
FollowLastG+≅ g c =
  &≅ id≅ &string-split≅
  ≅∙ &⊕-distL≅
  ≅∙ ⊕≅
      (uninhabited→≅⊥ (disjoint-ε-char+ ∘g &-swap ∘g (char+⊗r→char+ ∘g id ,⊗ startsWith→char+) ,&p &-π₂))
      id≅
  ≅∙ ⊥⊕≅ _

¬FollowLast∘g : (f : g ⊢ h) → ⟨ c ∉FollowLast h ⟩ → ⟨ c ∉FollowLast g ⟩
¬FollowLast∘g f c∉FLh = c∉FLh ∘g (f ,⊗ id) ,&p f

module _
  (g : Grammar ℓg)
  (c : ⟨ Alphabet ⟩)
  (null : ε ⊢ g)
  (c∉FL : ⟨ c ∉FollowLast g ⟩)
  where

  ∉FollowLast→∉First : ⟨ c ∉First g ⟩
  ∉FollowLast→∉First =
    c∉FL ∘g (null ,⊗ id ∘g ⊗-unit-l⁻) ,&p id

-- module _
--   (g : Grammar ℓg)
--   (h : Grammar ℓh)
--   (c : ⟨ Alphabet ⟩)
--   (null : (ε ⊢ g) ⊎ (ε ⊢ h))
--   (c∉FLg : ⟨ c ∉FollowLast g ⟩)
--   (c∉FLh : ⟨ c ∉FollowLast h ⟩)
--   where

--   ∉FollowLast→∉First-⊕ : ⟨ c ∉First g ⟩ × ⟨ c ∉First h ⟩
--   ∉FollowLast→∉First-⊕ .fst = {!!}
--   ∉FollowLast→∉First-⊕ .snd = {!!}
