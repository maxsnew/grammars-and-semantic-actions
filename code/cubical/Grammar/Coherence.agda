open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coherence (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Combinators.Base as Combinators
open import Cubical.Categories.Monoidal.Combinators.Equations as Combinators

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    E : Grammar ℓE
    F : Grammar ℓF

private
  G = GRAMMAR ℓ-zero
  module G = MonoidalCategory G

opaque
  ⊗-assoc⁻4⊗-assoc :
    ∀ {A B C D E F : Grammar ℓ-zero}
    → isSetGrammar A
    → isSetGrammar B
    → isSetGrammar C
    → isSetGrammar D
    → isSetGrammar E
    → isSetGrammar F
    → ⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E}
      ,⊗ id {A = F}
      ∘g ⊗-assoc
      ≡ ⊗-assoc4 ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc ∘g ⊗-assoc⁻4
  ⊗-assoc⁻4⊗-assoc isSetA isSetB isSetC isSetD isSetE isSetF =
    α4⁻¹α G (_ , isSetA) (_ , isSetB) (_ , isSetC)
            (_ , isSetD) (_ , isSetE) (_ , isSetF)

⊗-unit*-l⊗-assoc :
  {A B : Grammar ℓ-zero}
  → isSetGrammar A
  → isSetGrammar B
  → ⊗-unit*-l {ℓ = ℓ-zero} {A = A} ,⊗ id {A = B} ∘g ⊗-assoc ≡ ⊗-unit*-l
⊗-unit*-l⊗-assoc isSetA isSetB =
  Combinators.ηα G (_ , isSetA) (_ , isSetB)

opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-unit-l⊗-assoc :
    {A B : Grammar ℓ-zero}
    → isSetGrammar A
    → isSetGrammar B
    → ⊗-unit-l {A = A} ,⊗ id {A = B} ∘g ⊗-assoc ≡ ⊗-unit-l
  ⊗-unit-l⊗-assoc isSetA isSetB =
    ⊗-unit-l ,⊗ id ∘g ⊗-assoc
      ≡⟨ cong ((⊗-unit*-l {ℓ-zero} ,⊗ id) ∘g_) ⊗-assoc⊗-intro ⟩
    (⊗-unit*-l {ℓ-zero} ,⊗ id) ∘g ⊗-assoc ∘g ⊗-intro (liftG {ℓ-zero}) id
      ≡⟨ cong (_∘g ⊗-intro liftG id) (⊗-unit*-l⊗-assoc isSetA isSetB) ⟩
    ⊗-unit-l
    ∎
