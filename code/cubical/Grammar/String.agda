open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Term.Base Alphabet

private
  variable
    w : String

char : Grammar ℓ-zero
char = LinΣ[ c ∈ ⟨ Alphabet ⟩ ] literal c

string : Grammar ℓ-zero
string = KL* char

⌈_⌉ : String → Grammar ℓ-zero
⌈ [] ⌉ = ε
⌈ c ∷ w ⌉ = literal c ⊗ ⌈ w ⌉

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  uniquely-supported-⌈w⌉ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w'
  uniquely-supported-⌈w⌉ [] [] p = refl
  uniquely-supported-⌈w⌉ [] (c' ∷ w') p =
    Empty.rec (¬cons≡nil p)
  uniquely-supported-⌈w⌉ (c ∷ w) [] p =
    Empty.rec
      (¬nil≡cons (p .fst .snd ∙ cong (_++ p .fst .fst .snd) (p .snd .fst)))
  uniquely-supported-⌈w⌉ (c ∷ w) (c' ∷ w') p =
    decRec
      (λ c≡c' → cong₂ _∷_ c≡c'
        (uniquely-supported-⌈w⌉ w w'
          (subst (⌈ w ⌉) (sym (cons-inj₂ (p .fst .snd ∙
            cong (_++ p .fst .fst .snd) (p .snd .fst)))) (p .snd .snd))))
      (λ ¬c≡c → Empty.rec
        (¬c≡c (sym (cons-inj₁
          (p .fst .snd ∙ cong (_++ p .fst .fst .snd) (p .snd .fst))))))
      (DiscreteAlphabet isFinSetAlphabet c c')

internalize : (w : String) → ⌈ w ⌉ w
internalize [] = refl
internalize (c ∷ w) = (([ c ] , w) , refl) , refl , internalize w

⌈w⌉→string : ⌈ w ⌉ ⊢ string
⌈w⌉→string {[]} = nil
⌈w⌉→string {c ∷ w} = cons ∘g LinΣ-intro c ,⊗ ⌈w⌉→string {w}

