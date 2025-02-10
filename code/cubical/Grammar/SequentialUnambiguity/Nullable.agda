open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Nullable (Alphabet : hSet ℓ-zero)where

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Term Alphabet

private
  variable
    ℓg ℓh : Level
    g h : Grammar ℓg

open StrongEquivalence

NullableG : Grammar ℓg → Grammar ℓg
NullableG g = ε & g

¬Nullable_ : Grammar ℓg → hProp ℓg
(¬Nullable g) .fst = uninhabited (NullableG g)
(¬Nullable g) .snd = isProp-uninhabited

¬Nullable→char+ : ⟨ ¬Nullable g ⟩ → g ⊢ char +
¬Nullable→char+ notnull =
  ⊕-elim
    (⊥-elim ∘g notnull ∘g &-swap)
    &-π₂
  ∘g &string-split≅ .fun

¬Nullable&char+≅ : ⟨ ¬Nullable g ⟩ → (g ≅ (g & (char +)))
¬Nullable&char+≅ ¬nullg =
  &string-split≅
  ≅∙ ⊕≅ (uninhabited→≅⊥ (¬nullg ∘g &-swap)) id≅
  ≅∙ ⊥⊕≅ _

char+→¬Nullable : g ⊢ char + → ⟨ ¬Nullable g ⟩
char+→¬Nullable e =
  disjoint-ε-char+'
  ∘g id ,&p e

¬Nullable∘g : (f : g ⊢ h) → ⟨ ¬Nullable h ⟩ → ⟨ ¬Nullable g ⟩
¬Nullable∘g f ¬nullh = ¬nullh ∘g id ,&p f

¬Nullable-char+ : ⟨ ¬Nullable (char +) ⟩
¬Nullable-char+ = disjoint-ε-char+

¬Nullable-&char+ : ⟨ ¬Nullable (g & (char +)) ⟩
¬Nullable-&char+ = ¬Nullable∘g &-π₂ ¬Nullable-char+

¬Nullable⊗l : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (g ⊗ h) ⟩
¬Nullable⊗l notnull =
  char+→¬Nullable (char+⊗l→char+ ∘g ¬Nullable→char+ notnull ,⊗ id)

¬Nullable⊗r : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (h ⊗ g) ⟩
¬Nullable⊗r notnull =
  char+→¬Nullable (char+⊗r→char+ ∘g id ,⊗ ¬Nullable→char+ notnull)
