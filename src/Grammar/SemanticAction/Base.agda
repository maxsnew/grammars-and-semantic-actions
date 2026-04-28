{-
  Semantic actions.

  Ported from Nathan Varner's `semantic-actions` branch
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.SemanticAction.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (uncurry)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Grammar Alphabet hiding (Δ)
open import Term Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' ℓA ℓB ℓC ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

Δ : Type ℓ → Grammar ℓ
Δ X = ⊕[ x ∈ X ] ⊤

Δ-intro : ∀ {X : Type ℓX} {B : X → Grammar ℓB} → ⊕[ x ∈ X ] B x ⊢ Δ X
Δ-intro = ⊕ᴰ-elim (λ x → σ x ∘g ⊤-intro)

Δ-absorb-r : ∀ {X : Type ℓ} → Δ X ⊗ ⊤ ⊢ Δ X
Δ-absorb-r = Δ-intro ∘g ⊕ᴰ-distL .fun

Δ-absorb-l : ∀ {X : Type ℓ} → ⊤ ⊗ Δ X ⊢ Δ X
Δ-absorb-l = Δ-intro ∘g ⊕ᴰ-distR .fun

SemanticAction : Grammar ℓA → Type ℓ → Type _
SemanticAction A X = A ⊢ Δ X

semact-pure : ∀ {X : Type ℓ} → X → SemanticAction A X
semact-pure x = σ x ∘g ⊤-intro

semact-map : ∀ {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → SemanticAction A X → SemanticAction A Y
semact-map f x = ⊕ᴰ-elim (λ a → σ (f a) ∘g ⊤-intro) ∘g x

semact-map-g : ∀ {X : Type ℓ} → A ⊢ B → SemanticAction B X → SemanticAction A X
semact-map-g f y = y ∘g f

semact-Δ : ∀ {X : Type ℓ} → SemanticAction (Δ X) X
semact-Δ = id

semact-concat :
  ∀ {X : Type ℓ} {Y : Type ℓ'}
  → SemanticAction A X → SemanticAction B Y
  → SemanticAction (A ⊗ B) (X × Y)
semact-concat x y =
  ⊕ᴰ-elim (λ a →
    ⊕ᴰ-elim (λ b → σ (a , b) ∘g ⊤-intro) ∘g ⊕ᴰ-distR .fun)
  ∘g ⊕ᴰ-distL .fun
  ∘g x ,⊗ y

semact-bind :
  ∀ {X : Type ℓ} {Y : Type ℓ'}
  → SemanticAction A X
  → (X → SemanticAction B Y)
  → SemanticAction (A ⊗ B) Y
semact-bind x f =
  ⊕ᴰ-elim (λ a → Δ-absorb-l ∘g id ,⊗ f a)
  ∘g ⊕ᴰ-distL .fun
  ∘g x ,⊗ id

semact-left : ∀ {X : Type ℓ} → SemanticAction A X → SemanticAction (A ⊗ B) X
semact-left x = semact-map fst (semact-concat x (semact-pure tt))

semact-right : ∀ {X : Type ℓ} → SemanticAction B X → SemanticAction (A ⊗ B) X
semact-right x = semact-map snd (semact-concat (semact-pure tt) x)

semact-surround :
  ∀ {ℓD} {D : Grammar ℓD} {X : Type ℓ}
  → SemanticAction B X
  → SemanticAction (A ⊗ B ⊗ D) X
semact-surround x = semact-right (semact-left x)

semact-⊕ :
  ∀ {X : Type ℓ}
  → SemanticAction A X → SemanticAction B X
  → SemanticAction (A ⊕ B) X
semact-⊕ x y = ⊕-elim x y

semact-disjunct :
  ∀ {X : Type ℓ} {Y : Type ℓ'}
  → SemanticAction A X → SemanticAction B Y
  → SemanticAction (A ⊕ B) (X Sum.⊎ Y)
semact-disjunct x y =
  semact-⊕ (semact-map Sum.inl x) (semact-map Sum.inr y)

semact-⊕ᴰ :
  ∀ {X : Type ℓX} {B : X → Grammar ℓB} {Y : X → Type ℓ}
  → ((x : X) → SemanticAction (B x) (Y x))
  → SemanticAction (⊕[ x ∈ X ] B x) (Σ X Y)
semact-⊕ᴰ f =
  ⊕ᴰ-elim (λ x → semact-map (x ,_) (f x))

semact-⊕ᴰ' :
  ∀ {X : Type ℓX} {B : X → Grammar ℓB} {Y : Type ℓ}
  → ((x : X) → SemanticAction (B x) Y)
  → SemanticAction (⊕[ x ∈ X ] B x) Y
semact-⊕ᴰ' f = ⊕ᴰ-elim f

semact-&ᴰ :
  ∀ {X : Type ℓX} {B : X → Grammar ℓB} {Y : Type ℓ}
  → (x : X) → SemanticAction (B x) Y
  → SemanticAction (&[ x ∈ X ] B x) Y
semact-&ᴰ x f = f ∘g π x

semact-&-left : ∀ {X : Type ℓ} → SemanticAction A X → SemanticAction (A & B) X
semact-&-left x = x ∘g π₁

semact-&-right : ∀ {X : Type ℓ} → SemanticAction B X → SemanticAction (A & B) X
semact-&-right x = x ∘g π₂

semact-⊥ : ∀ {X : Type ℓ} → SemanticAction ⊥ X
semact-⊥ = ⊥-elim

semact-⊥* : ∀ {X : Type ℓ} → SemanticAction (⊥* {ℓA}) X
semact-⊥* = ⊥*-elim

semact-lift : ∀ {ℓ' ℓA} {A : Grammar ℓA} {X : Type ℓ}
            → SemanticAction A X → SemanticAction (LiftG ℓ' A) X
semact-lift x = x ∘g lowerG

semact-rec :
  ∀ {X : Type ℓX} {F : X → Functor X} {Y : X → Type ℓ}
  → Algebra F (λ x → Δ (Y x))
  → (x : X) → SemanticAction (μ F x) (Y x)
semact-rec alg x = rec _ alg x

-- Recover the letter
semact-char : SemanticAction char ⟨ Alphabet ⟩
semact-char = Δ-intro

semact-* :
  ∀ {X : Type ℓ}
  → SemanticAction A X → SemanticAction (A *) (List X)
semact-* {A = A} x = semact-rec alg _
  where
  alg : Algebra (*Ty A) (λ _ → Δ (List _))
  alg _ = ⊕ᴰ-elim λ where
    nil  → semact-pure []
    cons → semact-map (uncurry _∷_)
             (semact-concat (semact-lift x) (semact-lift semact-Δ))

-- Recover the underlying string
semact-string : SemanticAction string String
semact-string = semact-* semact-char

semact-underlying : SemanticAction A String
semact-underlying = semact-map-g string-intro semact-string
