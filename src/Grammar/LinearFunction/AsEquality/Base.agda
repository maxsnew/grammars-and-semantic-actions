open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

module Grammar.LinearFunction.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE : Level
    A A1 : Grammar ℓA
    B A2 : Grammar ℓB
    C A3 : Grammar ℓC
    D A4 : Grammar ℓD
    E A5 : Grammar ℓE
    f f' f'' : A ⊢ B

opaque
  unfolding _⊗_
  _⟜_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⟜ B) w = ∀ (w' : String) → B w' → A (w' ++ w)

  _⊸_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⊸ B) w = ∀ (w' : String) → A w' → B (w ++ w')

  infixr 2 _⊸_
  infixl 2 _⟜_

opaque
  unfolding _⊗_ _⟜_
  ⟜-intro : A ⊗ B ⊢ C → B ⊢ C ⟜ A
  ⟜-intro e _ p w' q = e _ ((_ , Eq.refl) , (q , p))

  ⟜-app : A ⊗ (B ⟜ A) ⊢ B
  ⟜-app {B = B} _ ((_ , Eq.refl) , a , aToB) = aToB _ a

⟜-intro-ε : A ⊢ C → ε ⊢ C ⟜ A
⟜-intro-ε f = ⟜-intro (f ∘g ⊗-unit-r)

⟜-intro⁻ : A ⊢ B ⟜ C → C ⊗ A ⊢ B
⟜-intro⁻ f = ⟜-app ∘g id ,⊗ f

opaque
  unfolding _⟜_ _⊗_
  -- THE ORDER SWAPS!
  ⟜-curry : A ⟜ (B ⊗ C) ⊢ (A ⟜ B) ⟜ C
  ⟜-curry {A = A} = ⟜-intro (⟜-intro {C = A}(⟜-app ∘g ⊗-assoc))

opaque
  unfolding _⊸_ _⊗_ ⊗-intro
  ⊸-intro : A ⊗ B ⊢  C → A ⊢ B ⊸ C
  ⊸-intro e _ a w' b = e _ ((_ , Eq.refl) , a , b)

  ⊸-app : (A ⊸ B) ⊗ A ⊢ B
  ⊸-app {B = B} _ ((_ , Eq.refl) , aToB , a) = aToB _ a

⊸-intro⁻ : A ⊢ B ⊸ C → A ⊗ B ⊢ C
⊸-intro⁻ {B = B}{C = C} f = ⊸-app ∘g ⊗-intro f (id {A = B})

-- THE ORDER SWAPS!
⊸-mapCod : C ⊢ D → A ⊸ C ⊢ A ⊸ D
⊸-mapCod f = ⊸-intro (f ∘g ⊸-app)

⟜-mapCod : C ⊢ D → C ⟜ A ⊢ D ⟜ A
⟜-mapCod f = ⟜-intro (f ∘g ⟜-app)

⊸-mapDom : A ⊢ B → B ⊸ C ⊢ A ⊸ C
⊸-mapDom f = ⊸-intro (⊸-app ∘g id ,⊗ f)

⟜-mapDom : A ⊢ B → C ⟜ B ⊢ C ⟜ A
⟜-mapDom f = ⟜-intro (⟜-app ∘g f ,⊗ id)

⊸-curry : (A ⊗ B) ⊸ C ⊢ A ⊸ (B ⊸ C)
⊸-curry {C = C} = ⊸-intro (⊸-intro (⊸-app ∘g ⊗-assoc⁻))

⊸-intro-ε : A ⊢ C → ε ⊢ A ⊸ C
⊸-intro-ε f = ⊸-intro (f ∘g ⊗-unit-l)

⊸2-intro-ε : A1 ⊗ A2 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ C
⊸2-intro-ε {C = C} f = ⊸-curry ∘g ⊸-intro-ε f

⊸3-intro-ε : A1 ⊗ A2 ⊗ A3 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C
⊸3-intro-ε {C = C} f = ⊸-mapCod (⊸-curry {C = C}) ∘g ⊸2-intro-ε f

⊸4-intro-ε : A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C
⊸4-intro-ε {C = C} f = ⊸-mapCod (⊸-mapCod (⊸-curry {C = C})) ∘g ⊸3-intro-ε f

⊸5-intro-ε : A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ A5 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ A5 ⊸ C
⊸5-intro-ε {C = C} f = ⊸-mapCod (⊸-mapCod (⊸-mapCod ⊸-curry)) ∘g ⊸4-intro-ε f

-- applying a multi-argument function to the front of a substitution
⊸-app-l : (A ⊸ B) ⊗ A ⊗ D ⊢ B ⊗ D
⊸-app-l = (⊗-intro ⊸-app id ∘g ⊗-assoc)

⊸0⊗ : ε ⊢ C → D ⊢ C ⊗ D
⊸0⊗ f = f ,⊗ id ∘g ⊗-unit-l⁻

⊸1⊗ : ε ⊢ A1 ⊸ C → A1 ⊗ B ⊢ C ⊗ B
⊸1⊗ f = ⊸-app-l ∘g ⊸0⊗ f

⊸2⊗ : ε ⊢ A1 ⊸ A2 ⊸ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
⊸2⊗ f = ⊸-app-l ∘g ⊸1⊗ f

⊸2⊗' : A1 ⊗ A2 ⊢ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
⊸2⊗' f = f ,⊗ id ∘g ⊗-assoc

⊸3⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ D ⊢ C ⊗ D
⊸3⊗ f = ⊸-app-l ∘g ⊸2⊗ f

⊸4⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ D ⊢ C ⊗ D
⊸4⊗ f = ⊸-app-l ∘g ⊸3⊗ f

⊸5⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ A5 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ A5 ⊗ D ⊢ C ⊗ D
⊸5⊗ f = ⊸-app-l ∘g ⊸4⊗ f

⟜0⊗ : ε ⊢ C → D ⊢ D ⊗ C
⟜0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻

Element→Term : ↑ (A ⊸ B) → A ⊢ B
Element→Term {A = A} {B = B} f =
  ⊸-app
  ∘g ε-elim f ,⊗ id
  ∘g ⊗-unit-l⁻

Term→Element : A ⊢ B → ↑ (A ⊸ B)
Term→Element e = ⊸-intro (e ∘g ⊗-unit-l) [] ε-intro
