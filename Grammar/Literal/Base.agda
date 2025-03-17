open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Term.Base Alphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA
    c : ⟨ Alphabet ⟩

opaque
  literal : ⟨ Alphabet ⟩ → Grammar ℓ-zero
  literal c w = w ≡ [ c ]

  lit-intro : (literal c) [ c ]
  lit-intro = refl

  literal-elim : A [ c ] → literal c ⊢ A
  literal-elim {A = A} Ac w w≡[c] =
    subst A (sym w≡[c]) Ac

  isLangLiteral : ∀ c → isLang (literal c)
  isLangLiteral c w = isSetString w [ c ]

  literal-length1 : ∀ c w → literal c w → length w ≡ 1
  literal-length1 c [] p = Empty.rec (¬nil≡cons p)
  literal-length1 c (x ∷ []) p = refl
  literal-length1 c (x ∷ x₁ ∷ w) p = Empty.rec (¬cons≡nil (cons-inj₂ p))

＂_＂ : ⟨ Alphabet ⟩ → Grammar ℓ-zero
＂ c ＂ = literal c


isSetGrammarLiteral : ∀ c → isSetGrammar (literal c)
isSetGrammarLiteral c = isLang→isSetGrammar (isLangLiteral c)

literal* : ∀ {ℓ : Level} → ⟨ Alphabet ⟩ → Grammar ℓ
literal* {ℓ = ℓ} c = LiftG ℓ (literal c)
