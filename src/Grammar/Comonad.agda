-- TODO: better name?
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Comonad (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Transport
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Grammar.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Equivalence Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD


opaque
  unfolding _&_ ε
  ↑-repr : StrongEquivalence (A & ε) (⊕[ _ ∈ ↑ A ] ε)
  ↑-repr {A = A} .StrongEquivalence.fun w a = (transport (λ i → A (a .snd i) ) (a .fst)) , (a .snd)
  ↑-repr {A = A} .StrongEquivalence.inv w eps = (transport (λ i → A (eps .snd (~ i))) (eps .fst)) , (eps .snd)
  ↑-repr {A = A} .StrongEquivalence.sec = funExt λ w → funExt λ a → ΣPathP (transportTransport⁻ (λ i → A (a .snd i)) (a .fst) , refl)
  ↑-repr {A = A} .StrongEquivalence.ret = funExt λ w → funExt λ a → ΣPathP (transportTransport⁻ (λ i → A (a .snd (~ i))) (a .fst) , refl)
