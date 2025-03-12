open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.FollowLast (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Term Alphabet

open import Cubical.Foundations.Powerset.More

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    c : ⟨ Alphabet ⟩

open StrongEquivalence
open Powerset ⟨ Alphabet ⟩

FollowLastG : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
FollowLastG A c = (A ⊗ startsWith c) & A

FollowLastG+ : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
FollowLastG+ A c = (A ⊗ startsWith c) & (A & char +)

-- This is the version of FollowLast defined by Bruggemann-Klein and Wood, and
-- further used in Krishnaswami and Yallop
FollowLastG' : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
FollowLastG' A c = ((A & char +) ⊗ startsWith c) & A

FollowLastG'+ : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
FollowLastG'+ A c = ((A & char +) ⊗ startsWith c) & (A & char +)

FollowLastG'⊢FollowLastG : FollowLastG' A c ⊢ FollowLastG A c
FollowLastG'⊢FollowLastG = (π₁ ,⊗ id) ,&p id

_∉FollowLast'_ : ⟨ Alphabet ⟩ → Grammar ℓA → hProp ℓA
(c ∉FollowLast' A) .fst = uninhabited (FollowLastG' A c)
(c ∉FollowLast' A) .snd = isProp-uninhabited

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓA → hProp ℓA
(c ∉FollowLast A) .fst = uninhabited (FollowLastG A c)
(c ∉FollowLast A) .snd = isProp-uninhabited

¬FollowLast→¬FollowLast' : ⟨ c ∉FollowLast A ⟩ → ⟨ c ∉FollowLast' A ⟩
¬FollowLast→¬FollowLast' c∉FL' = c∉FL' ∘g FollowLastG'⊢FollowLastG

¬FollowLast'→¬FollowLast :
  ⟨ ¬Nullable A ⟩ → ⟨ c ∉FollowLast' A ⟩ → ⟨ c ∉FollowLast A ⟩
¬FollowLast'→¬FollowLast ¬nullA c∉FL =
  c∉FL ∘g ((id ,&p ¬Nullable→char+ ¬nullA ∘g &-Δ) ,⊗ id) ,&p id

-- It might be nice to have a version of this
-- at an arbitrary level, but I don't
-- want to refactor the powerset code rn
-- or use explicit lifts
¬FollowLast' : Grammar ℓ-zero → ℙ
¬FollowLast' A c = c ∉FollowLast' A

¬FollowLast : Grammar ℓ-zero → ℙ
¬FollowLast A c = c ∉FollowLast A

FollowLastG+≅ :
  Grammar ℓA → ⟨ Alphabet ⟩ →
  FollowLastG A c ≅ FollowLastG+ A c
FollowLastG+≅ A c =
  &≅ id≅ &string-split≅
  ≅∙ &⊕-distL≅
  ≅∙ ⊕≅
      (uninhabited→≅⊥ (disjoint-ε-char+ ∘g &-swap ∘g (char+⊗r→char+ ∘g id ,⊗ startsWith→char+) ,&p π₂))
      id≅
  ≅∙ ⊥⊕≅ _

∉FollowLast∘g : (f : A ⊢ B) → ⟨ c ∉FollowLast B ⟩ → ⟨ c ∉FollowLast A ⟩
∉FollowLast∘g f c∉FLh = c∉FLh ∘g (f ,⊗ id) ,&p f

module _
  (A : Grammar ℓA)
  (c : ⟨ Alphabet ⟩)
  (null : ε ⊢ A)
  (c∉FL : ⟨ c ∉FollowLast A ⟩)
  where

  ∉FollowLast→∉First : ⟨ c ∉First A ⟩
  ∉FollowLast→∉First =
    c∉FL ∘g (null ,⊗ id ∘g ⊗-unit-l⁻) ,&p id

