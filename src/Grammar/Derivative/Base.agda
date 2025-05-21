open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Derivative.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Top Alphabet
open import Grammar.Literal Alphabet
open import Grammar.String Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    c : ⟨ Alphabet ⟩
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB


-- Derivative of a grammar with respect to a character (from the right)
Dr : ⟨ Alphabet ⟩ → Grammar ℓA → Grammar ℓA
Dr c g = literal c ⊸ g

Dl : Grammar ℓA → ⟨ Alphabet ⟩ → Grammar ℓA
Dl g c = g ⟜ literal c

opaque
  unfolding _⟜_ literal _⊗_
  -- This is probably the core of it
  Dl-repr : ∀ w → Iso (Dl A c w) (A (c ∷ w))
  Dl-repr {c = c} w .Iso.fun f = f (c ∷ []) refl
  Dl-repr {A = A} w .Iso.inv a w' w'≡c = transport (λ i → A (w'≡c (~ i) ++ w)) a
  Dl-repr w .Iso.rightInv = {!!}
  Dl-repr w .Iso.leftInv = {!!}

  -- starts-with-repr : ∀ c w → (p : (literal c ⊗ ⊤) w) → w ≡ c ∷ {!p!}
  -- starts-with-repr c w = {!!}

-- The "amazing right adjoint" to the derivative
√r : ⟨ Alphabet ⟩ → Grammar ℓA → Grammar ℓA
√r c A = (⊤ ⊗ literal c) ⇒ (A ⊗ literal c)

√l : ⟨ Alphabet ⟩ → Grammar ℓA → Grammar ℓA
√l c A = (literal c ⊗ ⊤) ⇒ (literal c ⊗ A)

opaque
  unfolding _⊸_ literal _⇒_ ⊤
  √l-app : ∀ {c} → Dl (√l c A) c ⊢ A
  √l-app {A = A}{c = c} w d = transport (λ i → A (uniq-splits i)) (bar .snd .snd)
    where
      foo : √l c A (c ∷ w)
      foo = d (c ∷ []) refl

      bar : (literal c ⊗ A) (c ∷ w)
      bar = foo ((((c ∷ [] , w)) , refl) , (refl , _))

      uniq-splits : bar .fst .fst .snd ≡ w
      uniq-splits =
        cons-inj₂ (sym (bar .fst .snd ∙ λ i → (bar .snd .fst i) ++ bar .fst .fst .snd))

  √l-λ : (Dl A c ⊢ B) → A ⊢ (√l c B)
  √l-λ {A = A}{c = c} f w a starts-c = starts-c .fst , (starts-c .snd .fst) ,
    f (starts-c .fst .fst .snd)
      (Dl-repr {A = A} {c = c} _ .Iso.inv (transport (λ i → A (foo i)) a))
    where 
      foo : w ≡ c ∷ starts-c .fst .fst .snd
      foo = starts-c .fst .snd ∙ cong (_++ starts-c .fst .fst .snd) (starts-c .snd .fst)

  -- TODO: βη
