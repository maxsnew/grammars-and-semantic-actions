open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Term Alphabet
open import Helper

private
  variable ℓg ℓh : Level

FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = (g ⊗ ＂ c ＂ ⊗ ⊤) & g

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ ⊤) & g

NullableG : Grammar ℓg → Grammar ℓg
NullableG g = ε & g

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → Type ℓg
c ∉FollowLast g = uninhabited (FollowLastG g c)

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → Type ℓg
c ∉First g = uninhabited (FirstG g c)

¬Nullable_ : Grammar ℓg → Type ℓg
¬Nullable g = uninhabited (NullableG g)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  open DecidablePowerset ⟨ Alphabet ⟩
  open DecidableFinitePowerset (⟨ Alphabet ⟩ , isFinSetAlphabet)

  -- A deterministic regular expression is parametrized
  -- by its follow last set, first last set, and nullability
  data DetReg : Decℙ → Decℙ → Bool → Type (ℓ-suc ℓ-zero) where
    ε-DetReg : DetReg ∅ℙ ∅ℙ true
    ⊥-DetReg : DetReg ∅ℙ ∅ℙ false
    _⊗DetReg[_]_ :
      ∀ {FL FL' F F' : Decℙ} {b' : Bool} →
      DetReg FL F false →
      FL ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' b' →
      DetReg
        (if b' then
        FL ∪ℙ F' ∪ℙ FL'
        else
        FL')
        F
        false
    literalDetReg : (c : ⟨ Alphabet ⟩) → DetReg ∅ℙ ⟦ c ⟧ℙ false
    _⊕DetReg[_]_ :
      ∀ {FL FL' F F' : Decℙ} {b b' : Bool} →
      DetReg FL F b →
      F ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' b' →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        (b or b')
    _*DetReg :
      ∀ {FL F : Decℙ} →
      DetReg FL F false →
      DetReg
        (F ∪ℙ FL)
        F
        true

  DetReg→Regex : ∀ {FL F} {b} → DetReg FL F b → Regex
  DetReg→Regex ε-DetReg = ε-Reg
  DetReg→Regex ⊥-DetReg = ⊥-Reg
  DetReg→Regex (r ⊗DetReg[ _ ] r') =
    (DetReg→Regex r) ⊗Reg (DetReg→Regex r')
  DetReg→Regex (literalDetReg c) = literalReg c
  DetReg→Regex (r ⊕DetReg[ _ ] r') =
    (DetReg→Regex r) ⊕Reg (DetReg→Regex r')
  DetReg→Regex (r *DetReg) =
    KL*Reg (DetReg→Regex r)

  DetReg→Grammar : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  DetReg→Grammar r = ⟦ DetReg→Regex r ⟧r

  ⟦_⟧DetReg : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  ⟦_⟧DetReg = DetReg→Grammar

  unambiguous-DetReg :
    ∀ {FL F} {b} (r : DetReg FL F b) → unambiguous (⟦ r ⟧DetReg)
  unambiguous-DetReg ε-DetReg = unambiguousε isFinSetAlphabet
  unambiguous-DetReg ⊥-DetReg = unambiguous⊥
  unambiguous-DetReg (r ⊗DetReg[ x ] r₁) = {!!}
  unambiguous-DetReg (literalDetReg c) = {!!}
  unambiguous-DetReg (r ⊕DetReg[ x ] r') =
    {!!}
    where
    unambig-r = unambiguous-DetReg r
    unambig-r' = unambiguous-DetReg r'
  unambiguous-DetReg (r *DetReg) = {!!}
