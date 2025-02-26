open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.First (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum hiding (rec)

open import Grammar Alphabet hiding (k)
open import Grammar.String.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Term Alphabet

open import Cubical.Foundations.Powerset.More

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    c : ⟨ Alphabet ⟩

open StrongEquivalence
open Powerset ⟨ Alphabet ⟩

FirstG : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
FirstG A c = startsWith c & A

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓA → hProp ℓA
(c ∉First A) .fst = uninhabited (FirstG A c)
(c ∉First A) .snd = isProp-uninhabited

-- Would like a universe polymorphic version of this.
-- Something something propositional resizing?
¬First : Grammar ℓ-zero → ℙ
¬First A c = c ∉First A

private
  ∉First⊗l-string : ⟨ ¬Nullable A ⟩ → ⟨ c ∉First A ⟩ → ⟨ c ∉First (A ⊗ string) ⟩
  ∉First⊗l-string {A = A} {c = c} ¬nullA c∉FA =
    ⊕-elim
      (⊥⊗ ∘g (¬nullA ∘g &-swap) ,⊗ id ∘g &-π₂)
      (⊕ᴰ-elim (λ c' →
        ⊕ᴰ-elim (λ c≡c' →
          (⊥⊗ ∘g
            (c∉FA ∘g
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

∉First⊗l : ⟨ ¬Nullable A ⟩ → ⟨ c ∉First A ⟩ → ⟨ c ∉First (A ⊗ B) ⟩
∉First⊗l {A = A} {c = c} {B = B} ¬nullA c∉FA =
  ∉First⊗l-string ¬nullA c∉FA
  ∘g id ,&p (id ,⊗ string-intro)

∉First∘g : (f : B ⊢ A) → ⟨ c ∉First A ⟩ → ⟨ c ∉First B ⟩
∉First∘g f c∉FA = c∉FA ∘g id ,&p f

∉First⊗ : ⟨ c ∉First A ⟩ → ⟨ c ∉First B ⟩ → ⟨ c ∉First (A ⊗ B) ⟩
∉First⊗ {A = A} {B = B} c∉FA c∉FB =
  ⊕-elim
    (c∉FB
    ∘g id ,&p (⊗-unit-l ∘g &-π₂ ,⊗ id))
    (∉First⊗l ¬Nullable-&char+ (∉First∘g &-π₁ c∉FA))
  ∘g &⊕-distL
  ∘g id ,&p (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id)


∉First-⊕ : ⟨ c ∉First A ⟩ → ⟨ c ∉First B ⟩ → ⟨ c ∉First (A ⊕ B) ⟩
∉First-⊕ c∉FA c∉FB =
  ⊕-elim c∉FA c∉FB
  ∘g &⊕-distL

∉First*-notnull : ⟨ ¬Nullable A ⟩ → ⟨ c ∉First A ⟩ → ⟨ c ∉First (A *) ⟩
∉First*-notnull ¬nullA c∉F =
  ⊕-elim
    (¬Nullable-startsWith ∘g &-swap)
    (∉First⊗l ¬nullA c∉F)
  ∘g &⊕-distL
  ∘g id ,&p *≅ε⊕A⊗A* _ .fun

∉First* : ⟨ c ∉First A ⟩ → ⟨ c ∉First (A *) ⟩
∉First* {c = c}{A = A} c∉F =
  ⇒-app
  ∘g &-swap
  ∘g id ,&p rec _ the-alg _
  where
  the-alg : Algebra (*Ty A) λ _ → ¬G (startsWith c)
  the-alg _ = ⊕ᴰ-elim λ {
      nil → ⇒-intro ¬Nullable-startsWith ∘g lowerG ∘g lowerG
    ; cons →
      ⇒-intro
        (⊕-elim
          (⇒-app
          ∘g (⊗-unit-l ∘g &-π₂ ,⊗ id) ,&p id)
          (∉First⊗l ¬Nullable-&char+ (∉First∘g &-π₁ c∉F) ∘g &-swap)
        ∘g &⊕-distR
        ∘g (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id) ,&p id)
      ∘g lowerG ,⊗ lowerG
    }

_#_ : Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
A # B = ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉First A ⟩ ⊎ ⟨ c ∉First B ⟩

#⊗l : ⟨ ¬Nullable A ⟩ → A # B → (A ⊗ C) # B
#⊗l ¬nullA sep c =
  Sum.map (∉First⊗l ¬nullA) (λ x → x) (sep c)

#∘g : A ⊢ B → B # C → A # C
#∘g f sep c = Sum.map (∉First∘g f) (λ x → x) (sep c)

#∘g2 : A ⊢ B → C ⊢ D → B # D → A # C
#∘g2 f f' sep c = Sum.map (∉First∘g f) (∉First∘g f') (sep c)

sym# : A # B → B # A
sym# sep c = Sum.rec inr inl (sep c)

#→disjoint :
  A # B →
  (⟨ ¬Nullable A ⟩ ⊎ ⟨ ¬Nullable B ⟩) →
  disjoint A B
#→disjoint sep ¬null =
  ⊕-elim
    (Sum.rec
      (λ ¬nullA → ¬nullA ∘g id ,&p &-π₁ ∘g &-swap)
      (λ ¬nullB → ¬nullB ∘g id ,&p &-π₂ ∘g &-swap)
      ¬null)
    (⊕ᴰ-elim (λ c →
      Sum.rec
        (λ c∉FA → c∉FA ∘g &-swap ∘g &-π₁ ,&p id)
        (λ c∉FB → c∉FB ∘g &-swap ∘g &-π₂ ,&p id)
        (sep c)
    )
    ∘g &⊕ᴰ-distR≅ .fun
    ∘g id ,&p ⊕ᴰ-distL .fun)
  ∘g &string-split≅ .fun
