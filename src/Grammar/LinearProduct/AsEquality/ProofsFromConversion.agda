open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.LinearProduct.AsEquality.ProofsFromConversion (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsEquality Alphabet

open import Grammar.LinearProduct.AsEquality.Base Alphabet
import Grammar.LinearProduct.Conversion Alphabet as Conversion

open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓG
      ℓH ℓK ℓL ℓM ℓN ℓO
      ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    E : Grammar ℓE
    F : Grammar ℓF
    G : Grammar ℓG
    H : Grammar ℓH
    K : Grammar ℓK
    L : Grammar ℓL
    M : Grammar ℓM
    N : Grammar ℓN
    O : Grammar ℓO
    f f' f'' f''' f'''' f''''' : A ⊢ B

opaque
  unfolding _⊗_ the-split ⊗-intro ⊗≡ ε
  ⊗-unit-rr⁻ :
    ∀ {A : Grammar ℓA}
    → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
  ⊗-unit-rr⁻ {A = A} = Conversion.⊗-unit-rr⁻

  ⊗-unit-r⁻r : ∀ {A : Grammar ℓA}
    → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
  ⊗-unit-r⁻r {A = A} = Conversion.⊗-unit-r⁻r

  cong-∘g⊗-unit-r⁻ :
    (e e' : A ⊗ ε ⊢ B) →
    (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
    e ≡ e'
  cong-∘g⊗-unit-r⁻ {A = A} f f' ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
    cong (_∘g ⊗-unit-r) ∘g≡ ∙
    cong (f' ∘g_) (⊗-unit-rr⁻)

  ⊗-unit*-rr⁻ :
    ⊗-unit*-r⁻ {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r ≡ id
  ⊗-unit*-rr⁻ {A = A} {ℓ = ℓ} i = ⊗-intro id liftG ∘g ⊗-unit-rr⁻ {A = A} i ∘g ⊗-intro id lowerG

  ⊗-unit*-r⁻r :
    ⊗-unit*-r {A = A} {ℓ = ℓ} ∘g ⊗-unit*-r⁻ ≡ id
  ⊗-unit*-r⁻r = ⊗-unit-r⁻r

open StrongEquivalence

εr≅ : A ≅ A ⊗ ε
εr≅ .fun = ⊗-unit-r⁻
εr≅ .inv = ⊗-unit-r
εr≅ .sec = ⊗-unit-rr⁻
εr≅ .ret = ⊗-unit-r⁻r

εl≅ : A ≅ ε ⊗ A
εl≅ .fun = ⊗-unit-l⁻
εl≅ .inv = ⊗-unit-l
εl≅ .sec = ⊗-unit-ll⁻
εl≅ .ret = ⊗-unit-l⁻l
