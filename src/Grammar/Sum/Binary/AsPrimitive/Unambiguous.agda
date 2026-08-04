open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.AsPrimitive.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Distributivity Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level

-- Converse of `unambig-⊕-is-disjoint` / `summand-{L,R}-is-unambig`:
-- the coproduct of two disjoint unambiguous grammars is unambiguous.
module _ {A : Grammar ℓA} {B : Grammar ℓB}
  (unambig-A : unambiguous A)
  (unambig-B : unambiguous B)
  (dis-AB : disjoint A B)
  where

  private
    init-A&B : is-initial (A & B)
    init-A&B = uninhabited→initial dis-AB

    init-B&A : is-initial (B & A)
    init-B&A = uninhabited→initial (dis-AB ∘g &-swap)

    case-AA : inl {A = A} {B = B} ∘g π₁ ≡ inl ∘g π₂
    case-AA = cong (inl ∘g_) (unambig-A π₁ π₂)

    case-BB : inr {A = B} {B = A} ∘g π₁ ≡ inr ∘g π₂
    case-BB = cong (inr ∘g_) (unambig-B π₁ π₂)

    case-AB : inl {A = A} {B = B} ∘g π₁ ≡ inr ∘g π₂
    case-AB = is-initial→propHoms init-A&B _ _

    case-BA : inr {A = B} {B = A} ∘g π₁ ≡ inl ∘g π₂
    case-BA = is-initial→propHoms init-B&A _ _

  opaque
    unfolding _⊕_ ⊕-elim _&_ &-intro π₁
    unambiguous⊕ : unambiguous (A ⊕ B)
    unambiguous⊕ = π≡→unambiguous the-π≡
      where
      inner-A : π₁ {A = A ⊕ B} {B = A ⊕ B} ∘g (inl ,&p id {A = A ⊕ B}) ∘g &⊕-distL⁻
              ≡ π₂ {A = A ⊕ B} {B = A ⊕ B} ∘g (inl ,&p id {A = A ⊕ B}) ∘g &⊕-distL⁻
      inner-A = ⊕≡ _ _ case-AA case-AB

      inner-B : π₁ {A = A ⊕ B} {B = A ⊕ B} ∘g (inr ,&p id {A = A ⊕ B}) ∘g &⊕-distL⁻
              ≡ π₂ {A = A ⊕ B} {B = A ⊕ B} ∘g (inr ,&p id {A = A ⊕ B}) ∘g &⊕-distL⁻
      inner-B = ⊕≡ _ _ case-BA case-BB

      lift-A : π₁ {A = A ⊕ B} {B = A ⊕ B} ∘g (inl ,&p id {A = A ⊕ B})
             ≡ π₂ {A = A ⊕ B} {B = A ⊕ B} ∘g (inl ,&p id {A = A ⊕ B})
      lift-A =
        cong ((π₁ ∘g (inl ,&p id {A = A ⊕ B})) ∘g_) (sym &⊕-distL-ret)
        ∙ cong (_∘g &⊕-distL) inner-A
        ∙ cong ((π₂ ∘g ((inl {B = A ⊕ B}) ,&p id)) ∘g_) &⊕-distL-ret

      lift-B : π₁ {A = A ⊕ B} {B = A ⊕ B} ∘g (inr ,&p id {A = A ⊕ B})
             ≡ π₂ {A = A ⊕ B} {B = A ⊕ B} ∘g (inr ,&p id {A = A ⊕ B})
      lift-B =
        cong ((π₁ ∘g (inr ,&p id {A = A ⊕ B})) ∘g_) (sym &⊕-distL-ret)
        ∙ cong (_∘g &⊕-distL) inner-B
        ∙ cong ((π₂ ∘g ((inr {B = A ⊕ B}) ,&p id)) ∘g_) &⊕-distL-ret

      outer : π₁ {A = A ⊕ B} {B = A ⊕ B} ∘g &⊕-distR⁻
            ≡ π₂ {A = A ⊕ B} {B = A ⊕ B} ∘g &⊕-distR⁻
      outer = ⊕≡ _ _ lift-A lift-B

      the-π≡ : π₁ {A = A ⊕ B} {B = A ⊕ B} ≡ π₂
      the-π≡ =
        cong (π₁ ∘g_) (sym &⊕-distR-ret)
        ∙ cong (_∘g &⊕-distR) outer
        ∙ cong (π₂ ∘g_) &⊕-distR-ret
