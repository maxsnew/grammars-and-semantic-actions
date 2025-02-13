open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet


private
  variable
    ℓG ℓH ℓS ℓ ℓ' ℓ'' ℓ''' : Level

LinearΠ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ {A = A} f w = ∀ (a : A) → f a w
&ᴰ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
&ᴰ = LinearΠ

LinearΣ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ {A = A} f w = Σ[ a ∈ A ] f a w
-- TODO: full rename?
⊕ᴰ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
⊕ᴰ = LinearΣ

⊕ᴰ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
⊕ᴰ-syntax = LinearΣ

LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ-syntax = LinearΣ

&ᴰ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
&ᴰ-syntax = LinearΠ

LinearΠ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ-syntax = LinearΠ

-- TODO: this precedence isn't really right
syntax LinearΣ-syntax {A = A} (λ x → B) = LinΣ[ x ∈ A ] B
syntax ⊕ᴰ-syntax {A = A} (λ x → B) = ⊕[ x ∈ A ] B
syntax LinearΠ-syntax {A = A} (λ x → B) = LinΠ[ x ∈ A ] B
syntax &ᴰ-syntax {A = A} (λ x → B) = &[ x ∈ A ] B

module _ {A : Type ℓS} {h : A → Grammar ℓH} where
  LinΠ-app : ∀ a → LinΠ[ a ∈ A ] h a ⊢ h a
  LinΠ-app = λ a w z → z a
  &ᴰ-π = LinΠ-app

  LinΣ-intro : ∀ a → h a ⊢ LinΣ[ a ∈ A ] h a
  LinΣ-intro = λ a w → _,_ a
  ⊕ᴰ-in = LinΣ-intro
module _ {A : Type ℓS} {g : Grammar ℓG}{h : A → Grammar ℓH} where
  LinΠ-intro : (∀ a → g ⊢ h a) → g ⊢ LinΠ[ a ∈ A ] h a
  LinΠ-intro = λ f w z a → f a w z
  &ᴰ-intro = LinΠ-intro

  &ᴰ-in = &ᴰ-intro

  LinΣ-elim : (∀ a → h a ⊢ g) → (LinΣ[ a ∈ A ] h a) ⊢ g
  LinΣ-elim f w x = f (fst x) w (snd x)
  ⊕ᴰ-elim = LinΣ-elim

  ⊕ᴰ≡ : (f f' : (⊕[ a ∈ A ] h a) ⊢ g)
    → (∀ a → f ∘g ⊕ᴰ-in a ≡ f' ∘g ⊕ᴰ-in a)
    → f ≡ f'
  ⊕ᴰ≡ f f' fa≡fa' i w x = fa≡fa' (x .fst) i w (x .snd)

  &ᴰ≡ : (f f' : g ⊢ (&[ a ∈ A ] h a))
    → (∀ a → &ᴰ-π a ∘g f ≡ &ᴰ-π a ∘g f')
    → f ≡ f'
  &ᴰ≡ f f' f≡ i w x a = f≡ a i w x

⊕ᴰ-elim∘g :
  ∀ {A : Type ℓ}{g : Grammar ℓ'}{h : A → Grammar ℓ''}{k : Grammar ℓ'''}
  → {f' : ∀ a → h a ⊢ g}
  → {f : g ⊢ k}
  → f ∘g ⊕ᴰ-elim f' ≡ ⊕ᴰ-elim (λ a → f ∘g f' a)
⊕ᴰ-elim∘g = ⊕ᴰ≡ _ _ (λ a → refl)

module _
  {A : Type ℓS}
  {g : A → Grammar ℓG}
  {h : A → Grammar ℓH}
  (e : (a : A) → g a ⊢ h a)
  where

  map⊕ᴰ : ⊕[ a ∈ A ] g a ⊢ ⊕[ a ∈ A ] h a
  map⊕ᴰ = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g e a)

  map&ᴰ : &[ a ∈ A ] g a ⊢ &[ a ∈ A ] h a
  map&ᴰ = &ᴰ-in λ a → e a ∘g &ᴰ-π a
