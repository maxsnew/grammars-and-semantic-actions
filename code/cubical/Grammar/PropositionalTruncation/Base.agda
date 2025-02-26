open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

module Grammar.PropositionalTruncation.Base (Alphabet : hSet ℓ-zero) where

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Grammar Alphabet hiding (k)
open import Grammar.HLevels.Base Alphabet
open import Grammar.HLevels.Properties Alphabet

open import Grammar.Subgrammar.Base Alphabet


open import Term Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

∥_∥ : Grammar ℓA → Grammar ℓA
∥ A ∥ w = PT.∥ A w ∥₁

trunc : A ⊢ ∥ A ∥
trunc w x = PT.∣ x ∣₁

unambiguous∥∥ : unambiguous ∥ A ∥
unambiguous∥∥ = EXTERNAL.isLang→unambiguous λ w → PT.isPropPropTrunc

elim∥∥ : unambiguous A → B ⊢ A → ∥ B ∥ ⊢ A
elim∥∥ unambig-A f w =
  PT.rec (EXTERNAL.unambiguous→isLang unambig-A w) (f w)

open StrongEquivalence

∥∥idem : unambiguous A → A ≅ ∥ A ∥
∥∥idem unambig-A =
  pointwiseIso→≅ _ _
    (λ w → pathToIso
      (sym (PT.propTruncIdempotent
             (EXTERNAL.unambiguous→isLang unambig-A w))))

module ∃Subgrammar (A : Grammar ℓA) (B : Grammar ℓB) where
  -- The subgrammar of g such that there exists an h parse
  -- over the same word
  ∃subgrammar : Grammar (ℓ-max ℓA ℓB)
  ∃subgrammar = unambiguous→subgrammar (unambiguous∥∥ {A = B}) A

  ∃-prop : A ⊢ Ω
  ∃-prop = unambiguous-prop (unambiguous∥∥ {A = B}) A

  open Subgrammar ∃-prop public

  witness∃ : ∃subgrammar ⊢ ∥ B ∥
  witness∃ = extract-pf sub-π sub-π-pf

  witness∃' : ∃subgrammar ⊢ A & ∥ B ∥
  witness∃' = sub-π ,& witness∃
