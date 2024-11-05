open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module SemanticAction.Length (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet
open import SemanticAction.Base Alphabet
open import Test Alphabet

open import Cubical.Data.Nat

length' : SemanticAction string ℕ
length' = semact-rec (λ _ → ⊕ᴰ-elim (λ {
    nil → ⊸-elim-ε (semact-pure 0)
  ; cons → ⊸-elim-ε
    (semact-map
      (uncurry _+_)
      (semact-concat (semact-pure 1) (semact-lift semact-Δ)))})) _

repeat→Δ : repeat char ⊢ Δ ℕ
repeat→Δ = ⊕ᴰ-elim (λ {(lift n) →
  rec (repeatTy char)
    (λ (lift n) → ⊕ᴰ-in n ∘g ⊤-intro)
    (lift n)})

-- TODO should be able to prove this using equalizers
-- after I merge the univprop for equalizer
sameLength : ⊸-elim-ε length' ≡ repeat→Δ ∘g grade char 
sameLength = {!!}
