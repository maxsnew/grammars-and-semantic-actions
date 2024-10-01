open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet


private
  variable
    ℓG ℓH ℓS : Level

LinearΠ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ {A = A} f w = ∀ (a : A) → f a w

LinearΣ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ {A = A} f w = Σ[ a ∈ A ] f a w

Dep⊕-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
Dep⊕-syntax = LinearΣ

LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ-syntax = LinearΣ

Dep&-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
Dep&-syntax = LinearΠ

LinearΠ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ-syntax = LinearΠ

-- TODO: this precedence isn't really right
syntax LinearΣ-syntax {A = A} (λ x → B) = LinΣ[ x ∈ A ] B
syntax Dep⊕-syntax {A = A} (λ x → B) = ⊕[ x ∈ A ] B
syntax LinearΠ-syntax {A = A} (λ x → B) = LinΠ[ x ∈ A ] B
syntax Dep&-syntax {A = A} (λ x → B) = &[ x ∈ A ] B

module _ {A : Type ℓS} {h : A → Grammar ℓH} where
  LinΠ-app : ∀ a → LinΠ[ a ∈ A ] h a ⊢ h a
  LinΠ-app = λ a w z → z a

  LinΣ-intro : ∀ a → h a ⊢ LinΣ[ a ∈ A ] h a
  LinΣ-intro = λ a w → _,_ a

module _ {A : Type ℓS} {g : Grammar ℓG}{h : A → Grammar ℓH} where
  LinΠ-intro : (∀ a → g ⊢ h a) → g ⊢ LinΠ[ a ∈ A ] h a
  LinΠ-intro = λ f w z a → f a w z

  LinΣ-elim : (∀ a → h a ⊢ g) → (LinΣ[ a ∈ A ] h a) ⊢ g
  LinΣ-elim f w x = f (fst x) w (snd x)

  ⊕ᴰ≡ : (f f' : (⊕[ a ∈ A ] h a) ⊢ g)
    → (∀ a → f ∘g LinΣ-intro a ≡ f' ∘g LinΣ-intro a)
    → f ≡ f'
  ⊕ᴰ≡ f f' fa≡fa' i w x = fa≡fa' (x .fst) i w (x .snd)

module _ {A : Type ℓS} {g : Grammar ℓG}{h : A → Grammar ℓH} where
  module _ {ℓk}{k : Grammar ℓk} where
    matchΣ-l :
      (∀ a → (h a) ⊗ g ⊢ k) →
      (LinΣ[ a ∈ A ] h a) ⊗ g ⊢ k
    matchΣ-l f = ⟜-intro⁻ (LinΣ-elim (λ a → ⟜-intro (f a)))

    matchΣ-r :
      (∀ a → g ⊗ (h a) ⊢ k) →
      g ⊗ LinΣ[ a ∈ A ] h a ⊢ k
    matchΣ-r f = ⊸-intro⁻ (LinΣ-elim (λ a → ⊸-intro (f a)))
