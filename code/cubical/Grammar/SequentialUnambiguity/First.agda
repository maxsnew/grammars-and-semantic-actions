open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.First (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Sum as Sum hiding (rec)

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Term Alphabet

open import Cubical.Foundations.Powerset.More

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl
    c : ⟨ Alphabet ⟩

open StrongEquivalence
open Powerset ⟨ Alphabet ⟩

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = startsWith c & g

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉First g) .fst = uninhabited (FirstG g c)
(c ∉First g) .snd = isProp-uninhabited

-- Would like a universe polymorphic version of this.
-- Something something propositional resizing?
¬First : Grammar ℓ-zero → ℙ
¬First g c = c ∉First g

private
  ∉First⊗l-string : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ string) ⟩
  ∉First⊗l-string {g = g} {c = c} ¬nullg c∉Fg =
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
  ∉First⊗l-string ¬nullg c∉Fg
  ∘g id ,&p (id ,⊗ string-intro)

∉First∘g : (f : h ⊢ g) → ⟨ c ∉First g ⟩ → ⟨ c ∉First h ⟩
∉First∘g f c∉Fg = c∉Fg ∘g id ,&p f

∉First⊗ : ⟨ c ∉First g ⟩ → ⟨ c ∉First h ⟩ → ⟨ c ∉First (g ⊗ h) ⟩
∉First⊗ {g = g} {h = h} c∉Fg c∉Fh =
  ⊕-elim
    (c∉Fh
    ∘g id ,&p (⊗-unit-l ∘g &-π₂ ,⊗ id))
    (∉First⊗l ¬Nullable-&char+ (∉First∘g &-π₁ c∉Fg))
  ∘g &⊕-distL
  ∘g id ,&p (⊗⊕-distR ∘g &string-split≅ .fun ,⊗ id)


∉First-⊕ : ⟨ c ∉First g ⟩ → ⟨ c ∉First h ⟩ → ⟨ c ∉First (g ⊕ h) ⟩
∉First-⊕ c∉Fg c∉Fh =
  ⊕-elim c∉Fg c∉Fh
  ∘g &⊕-distL

∉First*-notnull : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g *) ⟩
∉First*-notnull ¬nullg c∉F =
  ⊕-elim
    (¬Nullable-startsWith ∘g &-swap)
    (∉First⊗l ¬nullg c∉F)
  ∘g &⊕-distL
  ∘g id ,&p *≅ε⊕g⊗g* _ .fun

∉First* : ⟨ c ∉First g ⟩ → ⟨ c ∉First (g *) ⟩
∉First* {c = c}{g = g} c∉F =
  ⇒-app
  ∘g &-swap
  ∘g id ,&p rec _ the-alg _
  where
  the-alg : Algebra (*Ty g) λ _ → ¬G (startsWith c)
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

_#_ : Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
g # h = ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉First g ⟩ ⊎ ⟨ c ∉First h ⟩

#⊗l : ⟨ ¬Nullable g ⟩ → g # h → (g ⊗ k) # h
#⊗l ¬nullg sep c =
  Sum.map (∉First⊗l ¬nullg) (λ x → x) (sep c)

#∘g : g ⊢ h → h # k → g # k
#∘g f sep c = Sum.map (∉First∘g f) (λ x → x) (sep c)

#∘g2 : g ⊢ h → k ⊢ l → h # l → g # k
#∘g2 f f' sep c = Sum.map (∉First∘g f) (∉First∘g f') (sep c)

sym# : g # h → h # g
sym# sep c = Sum.rec inr inl (sep c)

#→disjoint :
  g # h →
  (⟨ ¬Nullable g ⟩ ⊎ ⟨ ¬Nullable h ⟩) →
  disjoint g h
#→disjoint sep ¬null =
  ⊕-elim
    (Sum.rec
      (λ ¬nullg → ¬nullg ∘g id ,&p &-π₁ ∘g &-swap)
      (λ ¬nullh → ¬nullh ∘g id ,&p &-π₂ ∘g &-swap)
      ¬null)
    (⊕ᴰ-elim (λ c →
      Sum.rec
        (λ c∉Fg → c∉Fg ∘g &-swap ∘g &-π₁ ,&p id)
        (λ c∉Fh → c∉Fh ∘g &-swap ∘g &-π₂ ,&p id)
        (sep c)
    )
    ∘g &⊕ᴰ-distR≅ .fun
    ∘g id ,&p ⊕ᴰ-distL .fun)
  ∘g &string-split≅ .fun
