open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.FollowLast (Alphabet : hSet ℓ-zero)where

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
