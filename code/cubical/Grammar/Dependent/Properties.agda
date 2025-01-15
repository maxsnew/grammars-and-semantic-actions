open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Function Alphabet
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
  disjointSummands⊕ᴰ : Type (ℓ-max ℓS ℓh)
  disjointSummands⊕ᴰ = ∀ a a' → (a ≡ a' → Empty.⊥) → disjoint (h a) (h a')

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
  {A : Type ℓS}
  {g : A → Grammar ℓg}
  {h : A → Grammar ℓh}
  (g≅h : ∀ (a : A) → g a ≅ h a)
  where

  &ᴰ≅ : (&[ a ∈ A ] g a) ≅ &[ a ∈ A ] h a
  &ᴰ≅ .fun = map&ᴰ λ a → g≅h a .fun
  &ᴰ≅ .inv = map&ᴰ λ a → g≅h a .inv
  &ᴰ≅ .sec = &ᴰ≡ _ _ λ a → cong (_∘g &ᴰ-π a) (g≅h a .sec)
  &ᴰ≅ .ret = &ᴰ≡ _ _ λ a → cong (_∘g &ᴰ-π a) (g≅h a .ret)

  ⊕ᴰ≅ : (⊕[ a ∈ A ] g a) ≅ ⊕[ a ∈ A ] h a
  ⊕ᴰ≅ .fun = map⊕ᴰ λ a → g≅h a .fun
  ⊕ᴰ≅ .inv = map⊕ᴰ λ a → g≅h a .inv
  ⊕ᴰ≅ .sec = ⊕ᴰ≡ _ _ λ a → cong (⊕ᴰ-in a ∘g_) (g≅h a .sec)
  ⊕ᴰ≅ .ret = ⊕ᴰ≡ _ _ λ a → cong (⊕ᴰ-in a ∘g_) (g≅h a .ret)

module _
  {A : Type ℓS}
  {g : A → Grammar ℓg}
  {h : Grammar ℓg}
  where

  private
    the-fun : (⊕[ a ∈ A ] g a) & h ⊢ ⊕[ a ∈ A ] (g a & h)
    the-fun = ⇒-intro⁻ (⊕ᴰ-elim (λ a → ⇒-intro (⊕ᴰ-in a)))

    the-inv : ⊕[ a ∈ A ] (g a & h) ⊢ (⊕[ a ∈ A ] g a) & h
    the-inv = ⊕ᴰ-elim λ a → ⊕ᴰ-in a ,&p id

    opaque
      unfolding ⇒-intro &-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec = refl

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret = refl

  &⊕ᴰ-distL≅ :
    (⊕[ a ∈ A ] g a) & h ≅ ⊕[ a ∈ A ] (g a & h)
  &⊕ᴰ-distL≅ = mkStrEq the-fun the-inv the-sec the-ret

  &⊕ᴰ-distR≅ :
    h & (⊕[ a ∈ A ] g a) ≅ ⊕[ a ∈ A ] (h & g a)
  &⊕ᴰ-distR≅ =
    &-swap≅
    ≅∙ &⊕ᴰ-distL≅
    ≅∙ ⊕ᴰ≅ λ a → &-swap≅

module _
  {X : Type ℓS} {A : X → Grammar ℓh}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

  isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
