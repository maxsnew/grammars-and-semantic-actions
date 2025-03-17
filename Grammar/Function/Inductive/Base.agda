open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function.Inductive.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Product.Binary.Inductive.Base Alphabet
import Grammar.Function.Cartesian.Base Alphabet as Fun
import Grammar.Product.Binary.Cartesian Alphabet as Prod
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Top.Base Alphabet
open import Term.Base Alphabet

open StrongEquivalence

private
  variable
    ℓA : Level
    A B C D : Grammar ℓA

  mk& : A Prod.& B ⊢ A & B
  mk& = Prod.&≅Ind& _ _ .fun

  mk&⁻ : A & B ⊢ A Prod.& B
  mk&⁻ = Prod.&≅Ind& _ _ .inv

_⇒_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
A ⇒ B = A Fun.⇒ B

⇒-intro :
  A & B ⊢ C →
  A ⊢ B ⇒ C
⇒-intro e = Fun.⇒-intro (e ∘g mk&)

⇒-app :
  (A ⇒ B) & A ⊢ B
⇒-app = Fun.⇒-app ∘g mk&⁻

⇒-intro⁻ :
  A ⊢ B ⇒ C
  → A & B ⊢ C
⇒-intro⁻ f = Fun.⇒-intro⁻ f ∘g mk&⁻
