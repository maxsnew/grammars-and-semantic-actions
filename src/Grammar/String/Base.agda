{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Erased.Data.List
import Erased.Data.Equality as Eq

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet

open import Grammar.Equivalence.Base Alphabet isSetAlphabet
-- open import Grammar.HLevels.Base Alphabet isSetAlphabet hiding (⟨_⟩)
open import Grammar.Sum.Base Alphabet isSetAlphabet
-- open import Grammar.Literal.Base Alphabet isSetAlphabet
-- open import Grammar.Epsilon Alphabet isSetAlphabet
-- open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
-- open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    w : String
    ℓA ℓB : Level
    A : Grammar ℓA

open StrongEquivalence

module _ {{monStr : MonoidalStr}} where
  open MonoidalStr monStr
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

  ⌈⌉→string : ∀ w → ⌈ w ⌉ ⊢ string
  ⌈⌉→string [] = NIL
  ⌈⌉→string (c ∷ w) = CONS ∘g σ c ,⊗ ⌈⌉→string w

  string→⌈⌉ : string ⊢ ⊕[ w ∈ String ] ⌈ w ⌉
  string→⌈⌉ = fold*r char
    (σ [])
    (⊕ᴰ-elim (λ c →
      ⊕ᴰ-elim (λ w → σ (c ∷ w))
      ∘g ⊕ᴰ-distR .fun)
      ∘g ⊕ᴰ-distL .fun)

  -- @0 ⌈_⌉' : String → Grammar ℓ-zero
  -- ⌈ w ⌉' w' = w ≡ w'

  -- opaque
  --   unfolding ⊗-intro ε literal
  --   mk⌈⌉ : ∀ w → ⌈ w ⌉ w
  --   mk⌈⌉ [] = Eq.refl
  --   mk⌈⌉ (c ∷ w) = (_ , Eq.refl) , (Eq.refl , (mk⌈⌉ w))

  -- @0 mk⌈⌉' : ∀ w → ⌈ w ⌉' w
  -- mk⌈⌉' w = refl

  -- @0 isLang⌈⌉' : ∀ w → isLang (⌈ w ⌉')
  -- isLang⌈⌉' = isSetString

  -- opaque
  --   unfolding ε _⊗_ literal
  --   @0 uniquely-supported-⌈⌉ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
  --   uniquely-supported-⌈⌉ [] [] p = refl
  --   uniquely-supported-⌈⌉ [] (x ∷ w') ()
  --   uniquely-supported-⌈⌉ (x ∷ w) [] ((_ , ()) , Eq.refl , the-⌈⌉)
  --   uniquely-supported-⌈⌉ (x ∷ w) (y ∷ w') ((_ , Eq.refl) , Eq.refl , the-⌈⌉) =
  --     cong (x ∷_) (uniquely-supported-⌈⌉ w w' the-⌈⌉)

  -- @0 ⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
  -- ⌈⌉→≡ = uniquely-supported-⌈⌉

  -- @0 ⌈⌉→⌈⌉' : ∀ w → ⌈ w ⌉ ⊢ ⌈ w ⌉'
  -- ⌈⌉→⌈⌉' = ⌈⌉→≡

  -- opaque
  --   unfolding ε _⊗_ uniquely-supported-⌈⌉ mk⌈⌉
  --   @0 ⌈⌉'→⌈⌉ : ∀ w → ⌈ w ⌉' ⊢ ⌈ w ⌉
  --   ⌈⌉'→⌈⌉ [] w p = Eq.sym (Eq.pathToEq p)
  --   ⌈⌉'→⌈⌉ (c ∷ w) w' cw≡w' = J (λ w'' cw≡w'' → (＂ c ＂ ⊗ ⌈ w ⌉) w'') (mk⌈⌉ (c ∷ w)) cw≡w'

  --   open StrongEquivalence
  --   @0 ⌈⌉≅⌈⌉' : ∀ w → ⌈ w ⌉ ≅ ⌈ w ⌉'
  --   ⌈⌉≅⌈⌉' w .fun = ⌈⌉→⌈⌉' w
  --   ⌈⌉≅⌈⌉' w .inv = ⌈⌉'→⌈⌉ w
  --   ⌈⌉≅⌈⌉' w .sec = funExt λ w' → funExt λ p → isSetString w w' _ _
  --   ⌈⌉≅⌈⌉' [] .ret = funExt λ w' → funExt λ p → isLangε _ _ _
  --   ⌈⌉≅⌈⌉' (c ∷ w) .ret = funExt λ w' → funExt λ @0 where
  --     ((_ , Eq.refl) , Eq.refl , the-⌈⌉) →
  --       Σ≡Prop (λ s → isProp× (isLangLiteral _ _) (isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w) _))
  --         (SplittingEq≡ (≡-× (transportRefl [ c ]) (transportRefl w ∙ ⌈⌉→⌈⌉' w _ the-⌈⌉)))

  -- @0 isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉
  -- isLang⌈⌉ w = isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w)

  -- @0 pick-parse : ∀ (w : String) → (A : Grammar ℓA) → A w → ⌈ w ⌉ ⊢ A
  -- pick-parse w A pA w' p⌈⌉ = subst A (uniquely-supported-⌈⌉ w w' p⌈⌉) pA


  -- mkstring : (w : String) → string w
  -- mkstring w = (⌈⌉→string w) w (mk⌈⌉ w)
