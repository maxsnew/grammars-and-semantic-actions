open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Sum.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Product.Binary.Cartesian.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet
open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB : Level

char : Grammar ℓ-zero
char = ⊕[ c ∈ ⟨ Alphabet ⟩ ] literal c

char-intro : ∀ (c : ⟨ Alphabet ⟩) → char [ c ]
char-intro c = (σ {A = λ c' → ＂ c' ＂} c) [ c ] lit-intro

string : Grammar ℓ-zero
string = char *

module _ (c : ⟨ Alphabet ⟩)
  where
  startsWith : Grammar ℓ-zero
  startsWith = ＂ c ＂ ⊗ string


stringL : Grammar ℓ-zero
stringL = *L char

⌈_⌉ : String → Grammar ℓ-zero
⌈ [] ⌉ = ε
⌈ c ∷ w ⌉ = literal c ⊗ ⌈ w ⌉

opaque
  unfolding ⊗-intro
  mk⌈⌉ : ∀ w → ⌈ w ⌉ w
  mk⌈⌉ [] = ε-intro
  mk⌈⌉ (c ∷ w) = (_ , refl) , (lit-intro , (mk⌈⌉ w))

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

pick-parse : ∀ (w : String) → (B : Grammar ℓB) → B w → ⌈ w ⌉ ⊢ B
pick-parse w B pB w' p⌈⌉ = subst B (uniquely-supported-⌈⌉ w w' p⌈⌉) pB

opaque
  unfolding ε literal _⊗_
  internalize : (w : String) → ⌈ w ⌉ w
  internalize [] = refl
  internalize (c ∷ w) = (([ c ] , w) , refl) , refl , internalize w

  ⌈w⌉→string : ⌈ w ⌉ ⊢ string
  ⌈w⌉→string {[]} = NIL
  ⌈w⌉→string {c ∷ w} = CONS ∘g σ c ,⊗ ⌈w⌉→string {w}

  mkstring : (s : String) → string s
  mkstring s = (⌈w⌉→string {w = s}) s (internalize s)

opaque
  unfolding _&_
  mk&⌈⌉ :
    (A : Grammar ℓA) →
    {w : String} →
    (p : A w) →
    (A & ⌈ w ⌉) w
  mk&⌈⌉ A {w = w} p =
    p , (mk⌈⌉ w)

⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
⌈⌉→≡ = uniquely-supported-⌈⌉

mkstring' : (s : String) → string s
mkstring' [] = NIL [] ε-intro
mkstring' (c ∷ w) =
  CONS (c ∷ w) (⊗-in (char-intro c) (mkstring' w))

parse-string : {A : Grammar ℓA} → string ⊢ A → (s : String) → A s
parse-string e s = e s (mkstring' s)
