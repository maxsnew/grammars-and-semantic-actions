open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓG ℓH ℓK : Level
    g : Grammar ℓG
    h : Grammar ℓH

opaque
  ε : Grammar ℓ-zero
  ε w = w ≡ []

  ε-intro : ε⊢ ε
  ε-intro = refl

  ε-elim : ∀ {g : Grammar ℓG}
    → ε⊢ g
    → ε ⊢ g
  ε-elim {g = g} g[] w w≡[] = subst g (sym w≡[]) g[]

  ε-β : ∀ (gp : ε⊢ g)
    → ε-elim {g = g} gp ∘ε ε-intro ≡ gp
  ε-β {g = g} gp = transportRefl gp

  ε-η : ∀ {g : Grammar ℓG}
   → (f : ε ⊢ g)
   → f ≡ ε-elim (f _ ε-intro)
  ε-η {g = g} f = funExt λ w → funExt λ w≡[] →
    J (λ w []≡w → f w (sym []≡w) ≡ subst g []≡w (f [] ε-intro))
      (sym (substRefl {B = g} (f [] ε-intro)))
      (sym w≡[])
  ε-elim-l : g ⊢ h → ε ,, g ⊢ h
  ε-elim-l {h = h} f w1 w2 (w1≡[]) gp =
    subst h
      (cong (_++ w2) (sym w1≡[]))
      (f w2 gp)

  ε-elim-r : g ⊢ h → g ,, ε ⊢ h
  ε-elim-r {h = h} f w1 w2 gp (w2≡[]) =
    subst h
      (sym (++-unit-r _) ∙ cong (w1 ++_) (sym w2≡[]))
      (f w1 gp)

  isLangε : isLang ε
  isLangε _ _ _ = isSetString _ _ _ _

  isSetGrammarε : isSetGrammar ε
  isSetGrammarε = isLang→isSetGrammar isLangε

ε* : ∀ {ℓ : Level} → Grammar ℓ
ε* {ℓ = ℓ} = LiftG ℓ ε

isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
isLangε* = isLangLift isLangε

isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
isSetGrammarε* = isLang→isSetGrammar isLangε*

