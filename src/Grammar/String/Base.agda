{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet hiding (⟨_⟩)
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Literal.Base Alphabet isSetAlphabet
open import Grammar.Epsilon Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.AsEquality.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    w : String
    ℓA ℓB : Level
    A : Grammar ℓA

char : Grammar ℓ-zero
char = ⊕[ c ∈ Alphabet ] literal c

module _ (c : Alphabet) where
  literal→char : ＂ c ＂ ⊢ char
  literal→char = σ c

string : Grammar ℓ-zero
string = char *

module _ (c : Alphabet) where
  startsWith : Grammar ℓ-zero
  startsWith = ＂ c ＂ ⊗ string

stringL : Grammar ℓ-zero
stringL = *L char

⌈_⌉ : String → Grammar ℓ-zero
⌈ [] ⌉ = ε
⌈ c ∷ w ⌉ = literal c ⊗ ⌈ w ⌉

-- ⌈_⌉' : String → Grammar ℓ-zero
-- ⌈ w ⌉' w' = w ≡ w'

-- opaque
--   unfolding ⊗-intro ε literal
--   mk⌈⌉ : ∀ w → ⌈ w ⌉ w
--   mk⌈⌉ [] = Eq.refl
--   mk⌈⌉ (c ∷ w) = (_ , Eq.refl) , (Eq.refl , (mk⌈⌉ w))

-- mk⌈⌉' : ∀ w → ⌈ w ⌉' w
-- mk⌈⌉' w = refl

-- @0 isLang⌈⌉' : ∀ w → isLang (⌈ w ⌉')
-- isLang⌈⌉' = isSetString

-- opaque
--   unfolding ε _⊗_ literal
--   uniquely-supported-⌈⌉ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
--   uniquely-supported-⌈⌉ [] [] p = refl
--   uniquely-supported-⌈⌉ [] (x ∷ w') ()
--   uniquely-supported-⌈⌉ (x ∷ w) [] ((_ , ()) , Eq.refl , the-⌈⌉)
--   uniquely-supported-⌈⌉ (x ∷ w) (y ∷ w') ((_ , Eq.refl) , Eq.refl , the-⌈⌉) =
--     cong (x ∷_) (uniquely-supported-⌈⌉ w w' the-⌈⌉)

-- ⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
-- ⌈⌉→≡ = uniquely-supported-⌈⌉

-- ⌈⌉→⌈⌉' : ∀ w → ⌈ w ⌉ ⊢ ⌈ w ⌉'
-- ⌈⌉→⌈⌉' = ⌈⌉→≡

-- opaque
--   unfolding ε _⊗_ uniquely-supported-⌈⌉ mk⌈⌉
--   ⌈⌉'→⌈⌉ : ∀ w → ⌈ w ⌉' ⊢ ⌈ w ⌉
--   ⌈⌉'→⌈⌉ [] w p = Eq.sym (Eq.pathToEq p)
--   ⌈⌉'→⌈⌉ (c ∷ w) w' cw≡w' = J (λ w'' cw≡w'' → (＂ c ＂ ⊗ ⌈ w ⌉) w'') (mk⌈⌉ (c ∷ w)) cw≡w'

--   open StrongEquivalence
--   ⌈⌉≅⌈⌉' : ∀ w → ⌈ w ⌉ ≅ ⌈ w ⌉'
--   ⌈⌉≅⌈⌉' w .fun = ⌈⌉→⌈⌉' w
--   ⌈⌉≅⌈⌉' w .inv = ⌈⌉'→⌈⌉ w
--   ⌈⌉≅⌈⌉' w .sec = funExt λ w' → funExt λ p → isSetString w w' _ _
--   ⌈⌉≅⌈⌉' [] .ret = funExt λ w' → funExt λ p → isLangε _ _ _
--   ⌈⌉≅⌈⌉' (c ∷ w) .ret = funExt λ w' → funExt λ @0 where
--     ((_ , Eq.refl) , Eq.refl , the-⌈⌉) →
--       Σ≡Prop (λ s → isProp× (isLangLiteral _ _) (isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w) _))
--         (Splitting≡ (≡-× (transportRefl [ c ]) (transportRefl w ∙ ⌈⌉→⌈⌉' w _ the-⌈⌉)))

-- @0 isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉
-- isLang⌈⌉ w = isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w)

-- pick-parse : ∀ (w : String) → (A : Grammar ℓA) → A w → ⌈ w ⌉ ⊢ A
-- pick-parse w A pA w' p⌈⌉ = subst A (uniquely-supported-⌈⌉ w w' p⌈⌉) pA

-- ⌈⌉→string : ∀ w → ⌈ w ⌉ ⊢ string
-- ⌈⌉→string [] = NIL
-- ⌈⌉→string (c ∷ w) = CONS ∘g σ c ,⊗ ⌈⌉→string w

-- mkstring : (w : String) → string w
-- mkstring w = (⌈⌉→string w) w (mk⌈⌉ w)
