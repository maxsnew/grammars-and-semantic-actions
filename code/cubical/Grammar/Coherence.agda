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
open import Term.Bilinear Alphabet
open import Term.Category Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g''' g'''' g''''' : Grammar ℓg
    h h' h'' h''' h'''' h''''' : Grammar ℓh
    f f' f'' f''' f'''' f''''' : g ⊢ h
    k : Grammar ℓk
    l : Grammar ℓl

private
  G = GRAMMAR ℓ-zero
  module G = MonoidalCategory G

opaque
  ⊗-assoc⁻4⊗-assoc :
    ∀ {g g' g'' g''' g'''' g''''' : Grammar ℓ-zero}
    → isSetGrammar g
    → isSetGrammar g'
    → isSetGrammar g''
    → isSetGrammar g'''
    → isSetGrammar g''''
    → isSetGrammar g'''''
    → ⊗-assoc⁻4 {g = g}{g' = g'}{g'' = g''}{g''' = g'''}{g'''' = g''''}
      ,⊗ id {g = g'''''}
      ∘g ⊗-assoc
      ≡ ⊗-assoc4 ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc ∘g ⊗-assoc⁻4
  ⊗-assoc⁻4⊗-assoc isSetG isSetG' isSetG'' isSetG''' isSetG'''' isSetG''''' =
    α4⁻¹α G (_ , isSetG) (_ , isSetG') (_ , isSetG'')
            (_ , isSetG''') (_ , isSetG'''') (_ , isSetG''''')

⊗-unit*-l⊗-assoc :
  {g g' : Grammar ℓ-zero}
  → isSetGrammar g
  → isSetGrammar g'
  → ⊗-unit*-l {ℓ = ℓ-zero} {g = g} ,⊗ id {g = g'} ∘g ⊗-assoc ≡ ⊗-unit*-l
⊗-unit*-l⊗-assoc isSetG isSetG' =
  Combinators.ηα G (_ , isSetG) (_ , isSetG')

opaque
  unfolding ⊗-intro ⊗-assoc
  ⊗-unit-l⊗-assoc :
    {g g' : Grammar ℓ-zero}
    → isSetGrammar g
    → isSetGrammar g'
    → ⊗-unit-l {g = g} ,⊗ id {g = g'} ∘g ⊗-assoc ≡ ⊗-unit-l
  ⊗-unit-l⊗-assoc isSetG isSetG' =
    ⊗-unit-l ,⊗ id ∘g ⊗-assoc
      ≡⟨ cong ((⊗-unit*-l {ℓ-zero} ,⊗ id) ∘g_) ⊗-assoc⊗-intro ⟩
    (⊗-unit*-l {ℓ-zero} ,⊗ id) ∘g ⊗-assoc ∘g ⊗-intro (liftG {ℓ-zero}) id
      ≡⟨ cong (_∘g ⊗-intro liftG id) (⊗-unit*-l⊗-assoc isSetG isSetG') ⟩
    ⊗-unit-l
    ∎
