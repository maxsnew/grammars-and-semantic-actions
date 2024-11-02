open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

module SemanticAction.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓS : Level
    A B : Type _

Δ : Type ℓS → Grammar ℓS
Δ X = ⊕[ x ∈ X ] ⊤

SemanticAction : Grammar ℓg → Type ℓS → Type _
SemanticAction g X = ε ⊢ (g ⊸ Δ X)

semact-map :
  {g : Grammar ℓg} →
  (f : A → B) → SemanticAction g A →
  SemanticAction g B
semact-map f x = ⊸-intro-ε (⊕ᴰ-elim (λ a → ⊕ᴰ-in (f a)) ∘g ⊸-elim-ε x)

semact-pure : {g : Grammar ℓg} → A → SemanticAction g A
semact-pure a = ⊸-intro-ε (⊕ᴰ-in a ∘g ⊤-intro)

semact-map-g :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  g ⊢ h → SemanticAction h A → SemanticAction g A
semact-map-g f x = ⊸-intro-ε (⊸-elim-ε x ∘g f)

semact-Δ : SemanticAction (Δ A) A
semact-Δ = ⊸-intro-ε id

semact-⊤ : {g : Grammar ℓg} → SemanticAction g Unit
semact-⊤ = semact-pure tt

semact-lift : {g : Grammar ℓg} → SemanticAction g A → SemanticAction (LiftG ℓh g) A
semact-lift = semact-map-g lowerG

semact-⊕ :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction g A → SemanticAction h A →
  SemanticAction (g ⊕ h) A
semact-⊕ x y = ⊸-intro-ε (⊕-elim (⊸-elim-ε x) (⊸-elim-ε y))

semact-disjunct :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction g A → SemanticAction h B →
  SemanticAction (g ⊕ h) (A ⊎ B)
semact-disjunct x y = semact-⊕ (semact-map inl x) (semact-map inr y)

semact-concat :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction g A → SemanticAction h B →
  SemanticAction (g ⊗ h) (A × B)
semact-concat x y = ⊸-intro-ε (
  ⊕ᴰ-elim (λ a →
    ⊕ᴰ-elim (λ b →
      ⊕ᴰ-in (a , b) ∘g ⊤-intro)
    ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
  ∘g ⊕ᴰ-distL .StrongEquivalence.fun
  ∘g ⊗-intro (⊸-elim-ε x) (⊸-elim-ε y))

semact-left :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction g A → SemanticAction (g ⊗ h) A
semact-left x = semact-map fst (semact-concat x semact-⊤)

semact-right :
  {g : Grammar ℓg} {h : Grammar ℓh} →
  SemanticAction h A → SemanticAction (g ⊗ h) A
semact-right x = semact-map snd (semact-concat semact-⊤ x)

semact-rec :
  {F : A → Functor A} {B : A → Type ℓS} →
  Algebra F (Δ ∘ B) → (a : A) → SemanticAction (μ F a) (B a)
semact-rec alg a = ⊸-intro-ε (rec _ alg a)

semact-* : {g : Grammar ℓg} → SemanticAction g A → SemanticAction (g *) (List A)
semact-* {g = g} x =
  ⊸-intro-ε (fold*r g (λ (lift tt) →
    ⊕ᴰ-elim λ where
      nil → ⊸-elim-ε (semact-pure [])
      cons → ⊸-elim-ε (semact-map (uncurry _∷_) (semact-concat
        (semact-map-g lowerG x)
        (semact-map-g lowerG semact-Δ)))))

semact-char : SemanticAction char ⟨ Alphabet ⟩
semact-char = ⊸-intro-ε (⊕ᴰ-elim (λ c → ⊸-elim-ε (semact-pure c)))

semact-string : SemanticAction string String
semact-string = semact-* semact-char

semact-underlying :
  {g : Grammar ℓg} →
  SemanticAction g (List ⟨ Alphabet ⟩)
semact-underlying =
  ⊸-intro-ε (⊸-elim-ε semact-string ∘g ⊤→string ∘g ⊤-intro)

semact-surround :
  {g : Grammar ℓg} {h : Grammar ℓh} {k : Grammar ℓk} →
  SemanticAction h A →
  SemanticAction (g ⊗ h ⊗ k) A
semact-surround x = semact-right (semact-left x)

