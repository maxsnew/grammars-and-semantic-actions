open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Derivative.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Derivative.Base Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level
    ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    X : Type ℓX
    Y : Type ℓY

-- Properties of the derivative
-- Many/most of these are not provable


-- Derivative commutes with coproducts. This says that literal c is
-- "connected". More generally it preserves all colimits which says
-- that it is "tiny"
opaque
  unfolding _⊸_ ⊸-intro ⊸-app literal

  D⊕ : (A : X → Grammar ℓA)
    (c : ⟨ Alphabet ⟩)
    → Inverse {A = ⊕[ x ∈ X ] Dr c (A x)}{B = Dr c (⊕[ x ∈ X ] A x) }
              (⊕ᴰ-elim (λ x → ⊸-intro (σ x ∘g ⊸-app)))
  D⊕ {X = X} A c .Inverse.inv w dr = (soln .fst) ,
    (λ w' w'≡c → transport (λ i → A (soln .fst) (w ++ w'≡c (~ i))) (soln .snd))
    where
      soln : Σ[ x ∈ X ] A x (w ++ c ∷ [])
      soln = dr (c ∷ []) refl
  D⊕ A c .Inverse.is-left-inv = funExt λ w → funExt λ s → {!!}
  D⊕ A c .Inverse.is-right-inv = {!!}

opaque
  Dlit : (c d : ⟨ Alphabet ⟩)
    → Inverse {A = ⊕[ _ ∈ c Eq.≡ d ] ε}{B = Dr c (literal d)}
        (⊕ᴰ-elim (λ { Eq.refl → ⊸-intro ⊗-unit-l }))
  Dlit c d .Inverse.inv = {!!}
  Dlit c d .Inverse.is-left-inv = {!!}
  Dlit c d .Inverse.is-right-inv = {!!}
