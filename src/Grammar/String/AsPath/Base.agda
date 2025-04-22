open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.String.AsPath.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Sum.Base Alphabet
open import Grammar.Literal.AsPath.Base Alphabet
open import Grammar.Epsilon.AsPath.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.AsPath.Base Alphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet
open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB : Level
    A : Grammar ℓA

char : Grammar ℓ-zero
char = ⊕[ c ∈ ⟨ Alphabet ⟩ ] literal c

module _ (c : ⟨ Alphabet ⟩) where
  literal→char : ＂ c ＂ ⊢ char
  literal→char = σ c

string : Grammar ℓ-zero
string = char *

module _ (c : ⟨ Alphabet ⟩) where
  startsWith : Grammar ℓ-zero
  startsWith = ＂ c ＂ ⊗ string

stringL : Grammar ℓ-zero
stringL = *L char

⌈_⌉ : String → Grammar ℓ-zero
⌈ [] ⌉ = ε
⌈ c ∷ w ⌉ = literal c ⊗ ⌈ w ⌉

⌈_⌉' : String → Grammar ℓ-zero
⌈ w ⌉' w' = w ≡ w'

opaque
  unfolding ⊗-intro ε literal
  mk⌈⌉ : ∀ w → ⌈ w ⌉ w
  mk⌈⌉ [] = refl
  mk⌈⌉ (c ∷ w) = (_ , refl) , (refl , (mk⌈⌉ w))

mk⌈⌉' : ∀ w → ⌈ w ⌉' w
mk⌈⌉' w = refl

isLang⌈⌉' : ∀ w → isLang (⌈ w ⌉')
isLang⌈⌉' = isSetString

opaque
  unfolding ε _⊗_ literal
  uniquely-supported-⌈⌉ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
  uniquely-supported-⌈⌉ [] [] p = refl
  uniquely-supported-⌈⌉ [] (x ∷ w') p =
    Empty.rec (¬cons≡nil p)
  uniquely-supported-⌈⌉ (x ∷ w) [] p =
    Empty.rec (¬nil≡cons (p .fst .snd ∙ cong (_++ p .fst .fst .snd) (p .snd .fst)))
  uniquely-supported-⌈⌉ (x ∷ w) (y ∷ w') p =
    cong₂ _∷_
      (cons-inj₁ w≡)
      (uniquely-supported-⌈⌉ w (p .fst .fst .snd) (p .snd .snd) ∙
        cons-inj₂ w≡)
    where
    w≡ : x ∷ p .fst .fst .snd ≡ y ∷ w'
    w≡ = ( (sym (cong (_++ p .fst .fst .snd) (p .snd .fst))) ∙ sym (p .fst .snd))

⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
⌈⌉→≡ = uniquely-supported-⌈⌉

⌈⌉→⌈⌉' : ∀ w → ⌈ w ⌉ ⊢ ⌈ w ⌉'
⌈⌉→⌈⌉' = ⌈⌉→≡

opaque
  unfolding ε _⊗_ uniquely-supported-⌈⌉ mk⌈⌉
  ⌈⌉'→⌈⌉ : ∀ w → ⌈ w ⌉' ⊢ ⌈ w ⌉
  ⌈⌉'→⌈⌉ [] = λ _ → sym
  ⌈⌉'→⌈⌉ (c ∷ w) w' cw≡w' = J (λ w'' cw≡w'' → (＂ c ＂ ⊗ ⌈ w ⌉) w'') (mk⌈⌉ (c ∷ w)) cw≡w'

  open StrongEquivalence
  ⌈⌉≅⌈⌉' : ∀ w → ⌈ w ⌉ ≅ ⌈ w ⌉'
  ⌈⌉≅⌈⌉' w .fun = ⌈⌉→⌈⌉' w
  ⌈⌉≅⌈⌉' w .inv = ⌈⌉'→⌈⌉ w
  ⌈⌉≅⌈⌉' w .sec = funExt λ w' → funExt λ p → isSetString w w' _ _
  ⌈⌉≅⌈⌉' [] .ret = funExt λ w' → funExt λ p → isSetString w' [] _ _
  ⌈⌉≅⌈⌉' (c ∷ w) .ret = funExt λ w' → funExt λ p →
    {!!}
    -- Σ≡Prop
    --  (λ s → isProp× (isLangLiteral c (s .fst .fst))
    --                 (isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w) (s .fst .snd)))
    --  (Splitting≡ (≡-× (transportRefl [ c ] ∙ sym (p .snd .fst))
    --              (transportRefl w ∙ ⌈⌉→⌈⌉' w _ (p .snd .snd))))

-- isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉
-- isLang⌈⌉ w = isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w)

-- pick-parse : ∀ (w : String) → (A : Grammar ℓA) → A w → ⌈ w ⌉ ⊢ A
-- pick-parse w A pA w' p⌈⌉ = subst A (uniquely-supported-⌈⌉ w w' p⌈⌉) pA

-- ⌈⌉→string : ∀ w → ⌈ w ⌉ ⊢ string
-- ⌈⌉→string [] = NIL
-- ⌈⌉→string (c ∷ w) = CONS ∘g σ c ,⊗ ⌈⌉→string w

-- mkstring : (w : String) → string w
-- mkstring w = (⌈⌉→string w) w (mk⌈⌉ w)
