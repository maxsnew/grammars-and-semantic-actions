
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

module Grammar.HLevels.MonoInjective (Alphabet : hSet ℓ-zero) where

open import Cubical.Functions.Embedding

open import Cubical.Data.FinSet
open import Cubical.Data.Unit

open import Grammar Alphabet
open import Term Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.String.Properties Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

pick-parse≡ : (w : String) → (x : g w) → (pick-parse w g x) w (mk⌈⌉ w) ≡ x
pick-parse≡ {g = g} w x =
  cong (λ a → transport (λ i → g (a i)) x) (isSetString _ _ _ _)
  ∙ transportRefl x

pick-parse≡' : (w : String) → (x y : g w) → pick-parse w g x ≡ pick-parse w g y → x ≡ y
pick-parse≡' {g = g} w x y parse≡ =
  sym (pick-parse≡ {g = g} w x)
  ∙ funExt⁻ (funExt⁻ parse≡ w) (mk⌈⌉ w)
  ∙ pick-parse≡ {g = g} w y

pick-parse-cong : (w : String) → (x y : g w) →
  (f : g ⊢ h) → (f w x ≡ f w y) →
  f ∘g pick-parse w g x ≡ f ∘g pick-parse w g y
pick-parse-cong {g = g} w x y f f≡ = funExt λ w' → funExt λ z →
  JDep {A = String }{B = λ w'' → ⌈ w ⌉ w'' }{x = w}{b = mk⌈⌉ w}
    (λ w'' w≡w'' ⌈w⌉w'' →
      λ ⌈⌉≡ →
    (f ∘g pick-parse w g x) w'' ⌈w⌉w''
      ≡
    (f ∘g pick-parse w g y) w'' ⌈w⌉w''
    )
    (cong (f w) (pick-parse≡ {g = g} w x) ∙ f≡ ∙ cong (f w) (sym (pick-parse≡ {g = g} w y)))
    (⌈⌉→≡ w w' z)
    (isProp→PathP (λ i → isLang⌈⌉ w (⌈⌉→≡ w w' z i)) _ _)

isMono→injective : {e : h ⊢ g} →
  isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
isMono→injective {h = h} {g = g} {e = e} mono-e w p p' ewp≡ =
  pick-parse≡' w p p' (mono-e (pick-parse w h p) (pick-parse w h p')
    (pick-parse-cong w p p' e ewp≡)
  )

isMono→hasPropFibers :
  {e : h ⊢ g} →
  isSetGrammar g →
  isMono e →
  (w : String) →
  hasPropFibers (e w)
isMono→hasPropFibers isSet-g mono-e w =
  injective→hasPropFibers (isSet-g w) (isMono→injective mono-e w _ _)
