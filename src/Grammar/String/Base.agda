{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Sum.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
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

⌈_⌉Eq : String → Grammar ℓ-zero
⌈ w ⌉Eq w' = w Eq.≡ w'

opaque
  unfolding ⊗-intro ε literal
  mk⌈⌉ : ∀ w → ⌈ w ⌉ w
  mk⌈⌉ [] = Eq.refl
  mk⌈⌉ (c ∷ w) = (_ , Eq.refl) , (Eq.refl , (mk⌈⌉ w))

mk⌈⌉' : ∀ w → ⌈ w ⌉' w
mk⌈⌉' w = refl

mk⌈⌉Eq : ∀ w → ⌈ w ⌉Eq w
mk⌈⌉Eq w = Eq.refl

isLang⌈⌉' : ∀ w → isLang (⌈ w ⌉')
isLang⌈⌉' = isSetString

isLang⌈⌉Eq : ∀ w → isLang (⌈ w ⌉Eq)
isLang⌈⌉Eq w = isSetEqString w

opaque
  unfolding ε _⊗_ literal
  uniquely-supported-⌈⌉Eq : ∀ w w' → ⌈ w ⌉ w' → w Eq.≡ w'
  uniquely-supported-⌈⌉Eq [] [] _ = Eq.refl
  uniquely-supported-⌈⌉Eq [] (x ∷ w') ()
  uniquely-supported-⌈⌉Eq (x ∷ w) [] (((w₁ , w₂) , e) , p₁ , _) =
    Eq.J (λ ww _ → [] Eq.≡ ww ++ w₂ → x ∷ w Eq.≡ [])
         (λ ()) (Eq.sym p₁) e
  uniquely-supported-⌈⌉Eq (x ∷ w) (y ∷ w') (((w₁ , w₂) , e) , p₁ , p) =
    Eq.ap (x ∷_) (uniquely-supported-⌈⌉Eq w w₂ p)
      Eq.∙ Eq.ap (_++ w₂) (Eq.sym p₁)
      Eq.∙ Eq.sym e

  uniquely-supported-⌈⌉ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
  uniquely-supported-⌈⌉ w w' p = Eq.eqToPath (uniquely-supported-⌈⌉Eq w w' p)

⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
⌈⌉→≡ = uniquely-supported-⌈⌉

⌈⌉→⌈⌉' : ∀ w → ⌈ w ⌉ ⊢ ⌈ w ⌉'
⌈⌉→⌈⌉' = ⌈⌉→≡

opaque
  unfolding ε _⊗_ uniquely-supported-⌈⌉ mk⌈⌉
  ⌈⌉'→⌈⌉ : ∀ w → ⌈ w ⌉' ⊢ ⌈ w ⌉
  ⌈⌉'→⌈⌉ [] = λ _ p → Eq.pathToEq (sym p)
  ⌈⌉'→⌈⌉ (c ∷ w) w' cw≡w' = J (λ w'' cw≡w'' → (＂ c ＂ ⊗ ⌈ w ⌉) w'') (mk⌈⌉ (c ∷ w)) cw≡w'

  open StrongEquivalence
  ⌈⌉≅⌈⌉' : ∀ w → ⌈ w ⌉ ≅ ⌈ w ⌉'
  ⌈⌉≅⌈⌉' w .fun = ⌈⌉→⌈⌉' w
  ⌈⌉≅⌈⌉' w .inv = ⌈⌉'→⌈⌉ w
  ⌈⌉≅⌈⌉' w .sec = funExt λ w' → funExt λ p → isSetString w w' _ _
  ⌈⌉≅⌈⌉' [] .ret = funExt λ w' → funExt λ p → isSetEqString w' [] _ _
  ⌈⌉≅⌈⌉' (c ∷ w) .ret = funExt λ w' → funExt λ p →
    isProp→PathP
      (λ _ → isPropLitTimes c w w')
      _ p
    where
    isPropLitTimes : (c : ⟨ Alphabet ⟩) (w w' : String)
      → isProp ((literal c ⊗ ⌈ w ⌉) w')
    isPropLitTimes c w w' (s , l , r) (s' , l' , r') =
      let
        sFst≡ : s .fst ≡ s' .fst
        sFst≡ = ≡-×
          (Eq.eqToPath l ∙ sym (Eq.eqToPath l'))
          (sym (⌈⌉→⌈⌉' w _ r) ∙ ⌈⌉→⌈⌉' w _ r')
        s≡ : s ≡ s'
        s≡ = SplittingEq≡ sFst≡
      in ΣPathP
        ( s≡
        , isProp→PathP
            (λ i → isProp× (isLangLiteral c (s≡ i .fst .fst))
                            (isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w) (s≡ i .fst .snd)))
            _ _ )

isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉
isLang⌈⌉ w = isLang≅ (sym≅ (⌈⌉≅⌈⌉' w)) (isLang⌈⌉' w)

⌈⌉→⌈⌉Eq : ∀ w → ⌈ w ⌉ ⊢ ⌈ w ⌉Eq
⌈⌉→⌈⌉Eq = uniquely-supported-⌈⌉Eq

opaque
  unfolding mk⌈⌉
  ⌈⌉Eq→⌈⌉ : ∀ w → ⌈ w ⌉Eq ⊢ ⌈ w ⌉
  ⌈⌉Eq→⌈⌉ w w' p = Eq.J (λ z _ → ⌈ w ⌉ z) (mk⌈⌉ w) p

  open StrongEquivalence
  ⌈⌉≅⌈⌉Eq : ∀ w → ⌈ w ⌉ ≅ ⌈ w ⌉Eq
  ⌈⌉≅⌈⌉Eq w .fun = ⌈⌉→⌈⌉Eq w
  ⌈⌉≅⌈⌉Eq w .inv = ⌈⌉Eq→⌈⌉ w
  ⌈⌉≅⌈⌉Eq w .sec = funExt λ w' → funExt λ p → isSetEqString w w' _ _
  ⌈⌉≅⌈⌉Eq w .ret = funExt λ w' → funExt λ p → isLang⌈⌉ w w' _ _

pick-parse : ∀ (w : String) → (A : Grammar ℓA) → A w → ⌈ w ⌉ ⊢ A
pick-parse w A pA w' p⌈⌉ = Eq.transport A (uniquely-supported-⌈⌉Eq w w' p⌈⌉) pA

⌈⌉-++ : ∀ w w' → ⌈ w ⌉ ⊗ ⌈ w' ⌉ ⊢ ⌈ w ++ w' ⌉
⌈⌉-++ [] w' = ⊗-unit-l
⌈⌉-++ (c ∷ w) w' = id ,⊗ ⌈⌉-++ w w' ∘g ⊗-assoc⁻

⌈⌉→string : ∀ w → ⌈ w ⌉ ⊢ string
⌈⌉→string [] = NIL
⌈⌉→string (c ∷ w) = CONS ∘g σ c ,⊗ ⌈⌉→string w

mkstring : (w : String) → string w
mkstring w = (⌈⌉→string w) w (mk⌈⌉ w)

opaque
  unfolding mk⌈⌉
            uniquely-supported-⌈⌉Eq uniquely-supported-⌈⌉
            ⌈⌉'→⌈⌉ ⌈⌉≅⌈⌉' ⌈⌉Eq→⌈⌉ ⌈⌉≅⌈⌉Eq
  unfoldStringDefs : Unit
  unfoldStringDefs = tt
