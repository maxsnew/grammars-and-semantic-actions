open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Derivative.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.List
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

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
  Dl-repr {c = c} w .Iso.fun f = f (c ∷ []) Eq.refl
  Dl-repr {A = A} w .Iso.inv a w' w'≡c =
    Eq.transport (λ ww → A (ww ++ w)) (Eq.sym w'≡c) a
  Dl-repr w .Iso.sec a = refl
  Dl-repr {A = A} {c = c} w .Iso.ret f = funExt λ w' → funExt λ where
    Eq.refl → refl

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
  √l-app {A = A}{c = c} w d = Eq.transport A uniq-splits-eq (bar .snd .snd)
    where
      foo : √l c A (c ∷ w)
      foo = d (c ∷ []) Eq.refl

      bar : (literal c ⊗ A) (c ∷ w)
      bar = foo ((((c ∷ [] , w)) , Eq.refl) , (Eq.refl , _))

      uniq-splits-eq : bar .fst .fst .snd Eq.≡ w
      uniq-splits-eq =
        Eq.sym
          (cons-inj₂Eq
            (Eq.transport (λ wl → c ∷ w Eq.≡ wl ++ bar .fst .fst .snd)
                          (bar .snd .fst)
                          (bar .fst .snd)))

  √l-λ : (Dl A c ⊢ B) → A ⊢ (√l c B)
  √l-λ {A = A}{c = c} f w a starts-c =
    starts-c .fst , (starts-c .snd .fst) ,
    f (starts-c .fst .fst .snd)
      (Dl-repr {A = A} {c = c} _ .Iso.inv (Eq.transport A fooEq a))
    where
      fooEq : w Eq.≡ c ∷ starts-c .fst .fst .snd
      fooEq = starts-c .fst .snd
            Eq.∙ Eq.ap (_++ starts-c .fst .fst .snd) (starts-c .snd .fst)

  -- TODO: βη
