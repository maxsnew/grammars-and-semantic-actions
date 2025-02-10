open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.First (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
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

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ string) & g

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉First g) .fst = uninhabited (FirstG g c)
(c ∉First g) .snd = isProp-uninhabited

¬First : Grammar ℓ-zero → ℙ
¬First g c = c ∉First g

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
