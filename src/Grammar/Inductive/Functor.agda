open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Functor (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Product.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet as ⊗Path
import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet as ⊗Eq
open import Grammar.Lift Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  data Functor (X : Type ℓX) : Type (ℓ-suc ℓX) where
    k : (A : Grammar ℓX) → Functor X
    Var : (x : X) → Functor X -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (Y : Type ℓX) → (F : Y → Functor X) → Functor X
    _⊗e_ : (F : Functor X) → (F' : Functor X) → Functor X
    _&e2_ : (F : Functor X) → (F' : Functor X) → Functor X

  infixr 25 _⊗e_
