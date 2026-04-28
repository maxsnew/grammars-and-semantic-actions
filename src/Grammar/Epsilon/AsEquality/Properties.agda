open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.AsEquality.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
import Grammar.Epsilon.AsPath.Base Alphabet as εPath
open import Grammar.Epsilon.AsEquality.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

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
  ε*≡ = funExt λ x → cong (Lift _) (funExt⁻ ε≡ x)

  isLangε : isLang ε
  isLangε = subst isLang ε≡ εPath.isLangε

  isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
  isLangε* {ℓ = ℓ} = subst isLang (ε*≡ {ℓ = ℓ}) εPath.isLangε*

  isSetGrammarε : isSetGrammar ε
  isSetGrammarε = subst isSetGrammar ε≡ εPath.isSetGrammarε

  isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
  isSetGrammarε* {ℓ = ℓ} = subst isSetGrammar (ε*≡ {ℓ = ℓ}) εPath.isSetGrammarε*

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

  ε-elim-natural : ∀ {A : Grammar ℓA} → (a : ε⊢ A) →
    (f : A ⊢ B) → f ∘g ε-elim {A = A} a ≡ ε-elim (f ∘ε a)
  ε-elim-natural a f =
    transport (λ i → f ∘g ε-elim≡ i a ≡ ε-elim≡ i (f ∘ε a))
      (εPath.ε-elim-natural a f)

  ε-β : ∀ (a : ε⊢ A) → ε-elim {A = A} a ∘ε ε-intro ≡ a
  ε-β {A = A} a = refl

  ε-length0 : ∀ w → ε w → length w ≡ 0
  ε-length0 _ Eq.refl = refl

opaque
  unfolding ε ε-intro ε-elim ε*-intro ε*-elim
            ε≡ ε*≡ ε-β ε-elim-natural ε-length0
            isLangε isLangε* isLangε≡
            isSetGrammarε isSetGrammarε*
            ε-intro≡ ε-elim≡
  unfoldEpsilonDefs : Unit
  unfoldEpsilonDefs = tt
