open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

module Grammar.PropositionalTruncation.Base (Alphabet : hSet ℓ-zero) where

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Grammar Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.HLevels.Properties Alphabet

open import Grammar.Subgrammar.Base Alphabet


open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    f f' f'' : g ⊢ h
    l : Grammar ℓl

∥_∥ : Grammar ℓg → Grammar ℓg
∥ g ∥ w = PT.∥ g w ∥₁

trunc : g ⊢ ∥ g ∥
trunc w x = PT.∣ x ∣₁

unambiguous∥∥ : unambiguous ∥ g ∥
unambiguous∥∥ = EXTERNAL.isLang→unambiguous λ w → PT.isPropPropTrunc

elim∥∥ : unambiguous g → h ⊢ g → ∥ h ∥ ⊢ g
elim∥∥ unambig-g f w =
  PT.rec (EXTERNAL.unambiguous→isLang unambig-g w) (f w)

open StrongEquivalence

∥∥idem : unambiguous g → g ≅ ∥ g ∥
∥∥idem unambig-g =
  pointwiseIso→≅ _ _
    (λ w → pathToIso
      (sym (PT.propTruncIdempotent
             (EXTERNAL.unambiguous→isLang unambig-g w))))

module ∃Subgrammar (g : Grammar ℓg) (h : Grammar ℓh) where
  -- The subgrammar of g such that there exists an h parse
  -- over the same word
  ∃subgrammar : Grammar (ℓ-max ℓg ℓh)
  ∃subgrammar = unambiguous→subgrammar (unambiguous∥∥ {g = h}) g

  ∃-prop : g ⊢ Ω
  ∃-prop = unambiguous-prop (unambiguous∥∥ {g = h}) g

  open Subgrammar ∃-prop public

  witness∃ : ∃subgrammar ⊢ ∥ h ∥
  witness∃ = extract-pf sub-π sub-π-pf

  witness∃' : ∃subgrammar ⊢ g & ∥ h ∥
  witness∃' = sub-π ,& witness∃
