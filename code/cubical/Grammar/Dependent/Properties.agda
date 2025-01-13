open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓg ℓh ℓS ℓS' : Level

open StrongEquivalence
module _ {A : Type ℓS} (h : A → Grammar ℓh) where
  disjointSummands : Type (ℓ-max ℓS ℓh)
  disjointSummands = ∀ a a' → (a ≡ a' → Empty.⊥) → disjoint (h a) (h a')

module _ {A : Type ℓS} {g : Grammar ℓg}{h : A → Grammar ℓh} where

  opaque
    unfolding _⊗_
    ⊕ᴰ-distL :
      StrongEquivalence
        ((⊕[ a ∈ A ] h a) ⊗ g)
        (⊕[ a ∈ A ] (h a ⊗ g))
    ⊕ᴰ-distL .fun w (s , (a , x) , y) = a , ((s , (x , y)))
    ⊕ᴰ-distL .inv w (a , (s , (x , y))) = s , ((a , x) , y)
    ⊕ᴰ-distL .sec = refl
    ⊕ᴰ-distL .ret = refl

    ⊕ᴰ-distR :
      StrongEquivalence
        (g ⊗ (⊕[ a ∈ A ] h a))
        (⊕[ a ∈ A ] (g ⊗ h a))
    ⊕ᴰ-distR .fun w (s , x , (a , y)) = a , ((s , (x , y)))
    ⊕ᴰ-distR .inv w (a , (s , (x , y))) = s , (x , (a , y))
    ⊕ᴰ-distR .sec = refl
    ⊕ᴰ-distR .ret = refl

    &ᴰ-strengthL :
        (&[ a ∈ A ] h a) ⊗ g ⊢ &[ a ∈ A ] (h a ⊗ g)
    &ᴰ-strengthL w (s , f , pg) a = s , (f a , pg)

    &ᴰ-strengthR :
        g ⊗ (&[ a ∈ A ] h a) ⊢ &[ a ∈ A ] (g ⊗ h a)
    &ᴰ-strengthR w (s , pg , f) a = s , (pg , f a)

module _
  {A : Type ℓS}
  {B : A → Type ℓS'}
  {h : Σ[ a ∈ A ] B a → Grammar ℓh}
  where
  &ᴰ⊕ᴰ-dist :
    (&[ a ∈ A ] (⊕[ b ∈ B a ] h (a , b))) ⊢ ⊕[ f ∈ (∀ (a : A) → B a) ] &[ a ∈ A ] h (a , f a)
  &ᴰ⊕ᴰ-dist w x = (λ a → x a .fst) , λ a → x a .snd

  &ᴰ⊕ᴰ-dist⁻ :
    ⊕[ f ∈ (∀ (a : A) → B a) ] &[ a ∈ A ] h (a , f a) ⊢ (&[ a ∈ A ] (⊕[ b ∈ B a ] h (a , b)))
  &ᴰ⊕ᴰ-dist⁻ = ⊕ᴰ-elim λ f → &ᴰ-in λ a → λ w x → (f a) , (x a)

  &ᴰ⊕ᴰ-dist≅  :
    ((&[ a ∈ A ] (⊕[ b ∈ B a ] h (a , b)))) ≅ (⊕[ f ∈ (∀ (a : A) → B a) ] &[ a ∈ A ] h (a , f a))
  &ᴰ⊕ᴰ-dist≅ .fun = &ᴰ⊕ᴰ-dist
  &ᴰ⊕ᴰ-dist≅ .inv = &ᴰ⊕ᴰ-dist⁻
  &ᴰ⊕ᴰ-dist≅ .sec = refl
  &ᴰ⊕ᴰ-dist≅ .ret = refl

module _
  {X : Type ℓS} {A : X → Grammar ℓh}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

  isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
