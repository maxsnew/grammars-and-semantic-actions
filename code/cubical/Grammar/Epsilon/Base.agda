open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet
open import Term.Bilinear Alphabet

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

  ε-elim : ∀ {A : Grammar ℓA}
    → ε⊢ A
    → ε ⊢ A
  ε-elim {A = A} A[] w w≡[] = subst A (sym w≡[]) A[]

  ε-β : ∀ (Ap : ε⊢ A)
    → ε-elim {A = A} Ap ∘ε ε-intro ≡ Ap
  ε-β {A = A} Ap = transportRefl Ap

  ε-η : ∀ {A : Grammar ℓA}
   → (f : ε ⊢ A)
   → f ≡ ε-elim (f _ ε-intro)
  ε-η {A = A} f = funExt λ w → funExt λ w≡[] →
    J (λ w []≡w → f w (sym []≡w) ≡ subst A []≡w (f [] ε-intro))
      (sym (substRefl {B = A} (f [] ε-intro)))
      (sym w≡[])
  ε-elim-l : A ⊢ B → ε ,, A ⊢ B
  ε-elim-l {B = B} f w1 w2 (w1≡[]) Ap =
    subst B
      (cong (_++ w2) (sym w1≡[]))
      (f w2 Ap)

  ε-elim-r : A ⊢ B → A ,, ε ⊢ B
  ε-elim-r {B = B} f w1 w2 Ap (w2≡[]) =
    subst B
      (sym (++-unit-r _) ∙ cong (w1 ++_) (sym w2≡[]))
      (f w1 Ap)

  isLangε : isLang ε
  isLangε _ _ _ = isSetString _ _ _ _

  isSetGrammarε : isSetGrammar ε
  isSetGrammarε = isLang→isSetGrammar isLangε

  ε-length0 : ∀ w → ε w → length w ≡ 0
  ε-length0 [] p = refl
  ε-length0 (x ∷ w) p = Empty.rec (¬cons≡nil p)

ε* : ∀ {ℓ : Level} → Grammar ℓ
ε* {ℓ = ℓ} = LiftG ℓ ε

isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
isLangε* = isLangLift isLangε

isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
isSetGrammarε* = isLang→isSetGrammar isLangε*
