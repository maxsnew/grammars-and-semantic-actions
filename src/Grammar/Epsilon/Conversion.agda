open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.Conversion (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.Epsilon.AsPath Alphabet
  renaming (ε to εPath
          ; ε* to ε*Path
          ; ε-intro to εPath-intro
          ; ε-elim to εPath-elim)
open import Grammar.Epsilon.AsEquality Alphabet
  renaming (ε to εEq
          ; ε* to ε*Eq
          ; ε-intro to εEq-intro
          ; ε-elim to εEq-elim)
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓ : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  unfolding εPath εEq

  ε≡ : εPath ≡ εEq
  ε≡ = funExt λ _ → Eq.PathPathEq

  ε*≡ : ε*Path {ℓ = ℓ} ≡ ε*Eq
  ε*≡ = funExt λ x → cong Lift (funExt⁻ ε≡ x)

  isLangεEq : isLang εEq
  isLangεEq = subst isLang ε≡ isLangε

  isLangε*Eq : isLang (ε*Eq {ℓ = ℓ})
  isLangε*Eq = subst isLang ε*≡ isLangε*

  isLangε≡ : ∀ i → isLang (ε≡ i)
  isLangε≡ i = subst-filler isLang ε≡ isLangε i

  ε-intro≡ : PathP (λ i → ε≡ i []) εPath-intro εEq-intro
  ε-intro≡ = isProp→PathP (λ i → isLangε≡ i []) _ _

  ε-elim≡ : PathP (λ i → ε⊢ A → ε≡ i ⊢ A) εPath-elim εEq-elim
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
    (f : A ⊢ B) → f ∘g εEq-elim {A = A} a ≡ εEq-elim (f ∘ε a)
  εEq-elim-natural a f =
    transport (λ i → f ∘g ε-elim≡ i a ≡ ε-elim≡ i (f ∘ε a)) (ε-elim-natural a f)

  εEq-β : ∀ (a : ε⊢ A) → εEq-elim {A = A} a ∘ε εEq-intro ≡ a
  εEq-β {A = A} a = transport (λ i → ε-elim≡ {A = A} i a ∘ε ε-intro≡ i ≡ a) (ε-β {A = A} a)

  isSetGrammarεEq : isSetGrammar εEq
  isSetGrammarεEq = subst isSetGrammar ε≡ isSetGrammarε

  isSetGrammarε*Eq : isSetGrammar (ε*Eq {ℓ = ℓ})
  isSetGrammarε*Eq = subst isSetGrammar ε*≡ isSetGrammarε*

  εEq-length0 : ∀ w → εEq w → length w ≡ 0
  εEq-length0 = transport (λ i → ∀ w → ε≡ i w → length w ≡ 0) ε-length0
