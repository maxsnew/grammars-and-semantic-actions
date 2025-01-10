open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

module _ {g : Grammar ℓg} {h : Grammar ℓh}
  (disjoint-summands : disjoint g h)
  (unambig-g : unambiguous g)
  (unambig-h : unambiguous h)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  open InductiveSum g h

  unambiguous-⊕Ind' : unambiguous ⊕Ind'
  unambiguous-⊕Ind' =
    mkUnambiguous⊕ᴰ
      (λ {
        L R → {!!}
      ; L L → {!!}
      ; R L → {!!}
      ; R R → {!!}
      })
      (λ {
        ⊕IndTag.L →
          unambiguous≅
            (comp-strong-equiv (LiftG≅ ℓh g) (LiftG≅ (ℓ-max ℓg ℓh) (LiftG ℓh g)))
            unambig-g
      ; ⊕IndTag.R →
          unambiguous≅
            (comp-strong-equiv (LiftG≅ ℓg h) (LiftG≅ (ℓ-max ℓg ℓh) (LiftG ℓg h)))
            unambig-h
       })
      isFinSetAlphabet
      (isFinSet→Discrete isFinSet⊕IndTag)

  unambiguous⊕ : unambiguous (g ⊕ h)
  unambiguous⊕ = {!!}
