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
open import Grammar.Dependent.Base Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Term.Base Alphabet

private
  variable
    w : String
    ℓh : Level

char : Grammar ℓ-zero
char = LinΣ[ c ∈ ⟨ Alphabet ⟩ ] literal c

char-intro : ∀ (c : ⟨ Alphabet ⟩) → char [ c ]
char-intro c = (⊕ᴰ-in {h = λ c' → ＂ c' ＂} c) [ c ] lit-intro

string : Grammar ℓ-zero
string = char *

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

pick-parse : ∀ (w : String) → (h : Grammar ℓh) → h w → ⌈ w ⌉ ⊢ h
pick-parse w h ph w' p⌈⌉ = subst h (uniquely-supported-⌈⌉ w w' p⌈⌉) ph

opaque
  unfolding ε literal _⊗_
  internalize : (w : String) → ⌈ w ⌉ w
  internalize [] = refl
  internalize (c ∷ w) = (([ c ] , w) , refl) , refl , internalize w

  ⌈w⌉→string : ⌈ w ⌉ ⊢ string
  ⌈w⌉→string {[]} = NIL
  ⌈w⌉→string {c ∷ w} = CONS ∘g ⊕ᴰ-in c ,⊗ ⌈w⌉→string {w}

  mkstring : (s : String) → string s
  mkstring s = (⌈w⌉→string {w = s}) s (internalize s)

mkstring' : (s : String) → string s
mkstring' [] = NIL [] ε-intro
mkstring' (c ∷ w) =
  CONS (c ∷ w) (⊗-in (char-intro c) (mkstring' w))

parse-string : {ℓg : Level}{g : Grammar ℓg} → string ⊢ g → (s : String) → g s
parse-string e s = e s (mkstring' s)
