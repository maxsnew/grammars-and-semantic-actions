open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Epsilon.AsPath.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB : Level
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

@0 isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
isLangε* = isLangLift isLangε

@0 isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
isSetGrammarε* = isLang→isSetGrammar isLangε*
