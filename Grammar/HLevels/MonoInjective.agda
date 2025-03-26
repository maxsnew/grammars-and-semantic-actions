open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

module Grammar.HLevels.MonoInjective (Alphabet : hSet ℓ-zero) where

open import Cubical.Functions.Embedding

open import Cubical.Data.FinSet
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.String.Base Alphabet
open import Term Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.String.Properties Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

pick-parse≡ : (w : String) → (x : A w) → (pick-parse w A x) w (mk⌈⌉ w) ≡ x
pick-parse≡ {A = A} w x =
  cong (λ a → transport (λ i → A (a i)) x) (isSetString _ _ _ _)
  ∙ transportRefl x

pick-parse≡' : (w : String) → (x y : A w) → pick-parse w A x ≡ pick-parse w A y → x ≡ y
pick-parse≡' {A = A} w x y parse≡ =
  sym (pick-parse≡ {A = A} w x)
  ∙ funExt⁻ (funExt⁻ parse≡ w) (mk⌈⌉ w)
  ∙ pick-parse≡ {A = A} w y

pick-parse-cong : (w : String) → (x y : A w) →
  (f : A ⊢ B) → (f w x ≡ f w y) →
  f ∘g pick-parse w A x ≡ f ∘g pick-parse w A y
pick-parse-cong {A = A} w x y f f≡ = funExt λ w' → funExt λ z →
  JDep {A = String }{B = λ w'' → ⌈ w ⌉ w'' }{x = w}{b = mk⌈⌉ w}
    (λ w'' w≡w'' ⌈w⌉w'' →
      λ ⌈⌉≡ →
    (f ∘g pick-parse w A x) w'' ⌈w⌉w''
      ≡
    (f ∘g pick-parse w A y) w'' ⌈w⌉w''
    )
    (cong (f w) (pick-parse≡ {A = A} w x) ∙ f≡ ∙ cong (f w) (sym (pick-parse≡ {A = A} w y)))
    (⌈⌉→≡ w w' z)
    (isProp→PathP (λ i → isLang⌈⌉ w (⌈⌉→≡ w w' z i)) _ _)

isMono→injective : {e : B ⊢ A} →
  isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
isMono→injective {B = B} {A = A} {e = e} mono-e w p p' ewp≡ =
  pick-parse≡' w p p' (mono-e (pick-parse w B p) (pick-parse w B p')
    (pick-parse-cong w p p' e ewp≡)
  )

isMono→hasPropFibers :
  {e : B ⊢ A} →
  isSetGrammar A →
  isMono e →
  (w : String) →
  hasPropFibers (e w)
isMono→hasPropFibers isSet-A mono-e w =
  injective→hasPropFibers (isSet-A w) (isMono→injective mono-e w _ _)
