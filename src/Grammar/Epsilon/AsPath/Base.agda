{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (lift ; Lift ; lower)
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.AsPath.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List
import Cubical.Data.Empty as Empty
open import Erased.Lift.Base
open import Cubical.Functions.FunExtEquiv

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓ : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  ε : Grammar ℓ-zero
  ε w = w ≡ []

  ε-intro : ε⊢ ε
  ε-intro = refl

  ε-elim : ∀ {A : Grammar ℓA} → ε⊢ A → ε ⊢ A
  ε-elim {A = A} A[] w w≡[] = subst A (sym w≡[]) A[]

  @0 ε-elim-natural : ∀ {A : Grammar ℓA} → (x : ε⊢ A) →
    (f : A ⊢ B) →
    f ∘g ε-elim {A = A} x ≡ ε-elim (f ∘ε x)
  ε-elim-natural {B = B} {A = A} x f = funExt λ w → funExt λ p →
    J (λ w' w'≡ → (f ∘g ε-elim x) w' (sym w'≡) ≡ ε-elim {A = B}(f ∘ε x) w' (sym w'≡))
      (cong (f []) (transportRefl x) ∙ sym (substRefl {A = A []} {B = λ _ → B []} {x = x} (f [] x)))
      (sym p)

  @0 ε-β : ∀ (Ap : ε⊢ A) → ε-elim {A = A} Ap ∘ε ε-intro ≡ Ap
  ε-β {A = A} Ap = transportRefl Ap

  @0 isLangε : isLang ε
  isLangε _ _ _ = isSetString _ _ _ _

  @0 isSetGrammarε : isSetGrammar ε
  isSetGrammarε = isLang→isSetGrammar isLangε

  @0 ε-length0 : ∀ w → ε w → length w ≡ 0
  ε-length0 [] p = refl
  ε-length0 (x ∷ w) p = Empty.rec (¬cons≡nil p)

ε* : ∀ {ℓ : Level} → Grammar ℓ
ε* {ℓ = ℓ} = LiftG ℓ ε

opaque
  unfolding ε
  ε*-intro : ε⊢ (ε* {ℓ = ℓ})
  ε*-intro = lift ε-intro

  ε*-elim : ∀ {A : Grammar ℓA} → ε⊢ A → (ε* {ℓ = ℓ}) ⊢ A
  ε*-elim {A = A} A[] w (lift w≡[]) = ε-elim {A = A} A[] w w≡[]

@0 isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
isLangε* = isLangLift isLangε

@0 isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
isSetGrammarε* = isLang→isSetGrammar isLangε*
