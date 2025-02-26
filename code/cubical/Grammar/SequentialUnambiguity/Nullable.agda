open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SequentialUnambiguity.Nullable (Alphabet : hSet ℓ-zero)where

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB
    c : ⟨ Alphabet ⟩

open StrongEquivalence

NullableG : Grammar ℓA → Grammar ℓA
NullableG A = ε & A

¬Nullable_ : Grammar ℓA → hProp ℓA
(¬Nullable A) .fst = uninhabited (NullableG A)
(¬Nullable A) .snd = isProp-uninhabited

¬Nullable→char+ : ⟨ ¬Nullable A ⟩ → A ⊢ char +
¬Nullable→char+ notnull =
  ⊕-elim
    (⊥-elim ∘g notnull ∘g &-swap)
    &-π₂
  ∘g &string-split≅ .fun

¬Nullable&char+≅ : ⟨ ¬Nullable A ⟩ → (A ≅ (A & (char +)))
¬Nullable&char+≅ ¬nullA =
  &string-split≅
  ≅∙ ⊕≅ (uninhabited→≅⊥ (¬nullA ∘g &-swap)) id≅
  ≅∙ ⊥⊕≅ _

char+→¬Nullable : A ⊢ char + → ⟨ ¬Nullable A ⟩
char+→¬Nullable e =
  disjoint-ε-char+'
  ∘g id ,&p e

¬Nullable∘g : (f : A ⊢ B) → ⟨ ¬Nullable B ⟩ → ⟨ ¬Nullable A ⟩
¬Nullable∘g f ¬nullB = ¬nullB ∘g id ,&p f

¬Nullable-char+ : ⟨ ¬Nullable (char +) ⟩
¬Nullable-char+ = disjoint-ε-char+

¬Nullable-&char+ : ⟨ ¬Nullable (A & (char +)) ⟩
¬Nullable-&char+ = ¬Nullable∘g &-π₂ ¬Nullable-char+

¬Nullable-startsWith : ⟨ ¬Nullable (startsWith c) ⟩
¬Nullable-startsWith = ¬Nullable∘g startsWith→char+ ¬Nullable-char+

¬Nullable⊗l : ⟨ ¬Nullable A ⟩ → ⟨ ¬Nullable (A ⊗ B) ⟩
¬Nullable⊗l notnull =
  char+→¬Nullable (char+⊗l→char+ ∘g ¬Nullable→char+ notnull ,⊗ id)

¬Nullable⊗r : ⟨ ¬Nullable A ⟩ → ⟨ ¬Nullable (B ⊗ A) ⟩
¬Nullable⊗r notnull =
  char+→¬Nullable (char+⊗r→char+ ∘g id ,⊗ ¬Nullable→char+ notnull)
