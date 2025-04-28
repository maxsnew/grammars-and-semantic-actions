{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lower)
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.AsEquality.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Lift.Base
open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
import Grammar.Epsilon.AsPath Alphabet isSetAlphabet as εPath
open import Grammar.Epsilon.AsEquality.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓ : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  unfolding εPath.ε ε

  ε≡ : εPath.ε ≡ ε
  ε≡ = funExt λ _ → Eq.PathPathEq

  ε*≡ : εPath.ε* {ℓ = ℓ} ≡ ε*
  ε*≡ = funExt λ x → cong Lift (funExt⁻ ε≡ x)

  isLangε : isLang ε
  isLangε = subst isLang ε≡ εPath.isLangε

  isLangε* : isLang (ε* {ℓ = ℓ})
  isLangε* = subst isLang ε*≡ εPath.isLangε*

  isLangε≡ : ∀ i → isLang (ε≡ i)
  isLangε≡ i = subst-filler isLang ε≡ εPath.isLangε i

  ε-intro≡ : PathP (λ i → ε≡ i []) εPath.ε-intro ε-intro
  ε-intro≡ = isProp→PathP (λ i → isLangε≡ i []) _ _

  ε-elim≡ : PathP (λ i → ε⊢ A → ε≡ i ⊢ A) εPath.ε-elim ε-elim
  ε-elim≡ {A = A} = funExt λ a → funExt λ w →
    funExtDep (λ where
      {εP} {Eq.refl} eps →
          subst A (sym εP) a
              ≡⟨ cong (λ z → subst A z a) (isSetString _ _ _ _) ⟩
          subst A refl a
              ≡⟨ substRefl {B = A} a ⟩
          a
          ∎)

  εEq-elim-natural : ∀ {A : Grammar ℓA} → (a : ε⊢ A) →
    (f : A ⊢ B) → f ∘g ε-elim {A = A} a ≡ ε-elim (f ∘ε a)
  εEq-elim-natural a f =
    transport (λ i → f ∘g ε-elim≡ i a ≡ ε-elim≡ i (f ∘ε a)) (εPath.ε-elim-natural a f)

  εEq-β : ∀ (a : ε⊢ A) → ε-elim {A = A} a ∘ε ε-intro ≡ a
  εEq-β {A = A} a = transport (λ i → ε-elim≡ {A = A} i a ∘ε ε-intro≡ i ≡ a) (εPath.ε-β {A = A} a)

  isSetGrammarε : isSetGrammar ε
  isSetGrammarε = subst isSetGrammar ε≡ εPath.isSetGrammarε

  isSetGrammarε* : isSetGrammar (ε* {ℓ = ℓ})
  isSetGrammarε* = subst isSetGrammar ε*≡ εPath.isSetGrammarε*

  εEq-length0 : ∀ w → ε w → length w ≡ 0
  εEq-length0 = transport (λ i → ∀ w → ε≡ i w → length w ≡ 0) εPath.ε-length0
