open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Bilinear (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Grammar.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

{-- A direct interpretation of terms of 2 variables
 -- x : A , y : B ⊢ M : C
 --
 --}
Bilinear : Grammar ℓA → Grammar ℓB → Grammar ℓC → Type _
Bilinear A B C = ∀ w1 w2 → A w1 → B w2 → C (w1 ++ w2)

_,,_⊢_ : Grammar ℓA → Grammar ℓB → Grammar ℓC → Type _
_,,_⊢_ = Bilinear

_∘b_ : C ⊢ D → A ,, B ⊢ C → A ,, B ⊢ D
_∘b_ f f' = λ w1 w2 Ap Bp → f (w1 ++ w2) (f' w1 w2 Ap Bp)

_b∘l_ : A ,, B ⊢ C → D ⊢ A → D ,, B ⊢ C
(f b∘l f') w1 w2 lp Bp = f w1 w2 (f' w1 lp) Bp

_b∘r_ : A ,, B ⊢ C → D ⊢ B → A ,, D ⊢ C
(f b∘r f') w1 w2 Ap lp = f w1 w2 Ap (f' w2 lp)

-- Does the fact that this is refl make anything easier?
-- TODO: should these be opaque?
_b∘εl_ : A ,, B ⊢ C → ε⊢ A → B ⊢ C
_b∘εl_ {C = C} f Ap w Bp =
   (f [] w Ap Bp)

_b∘εr_ : A ,, B ⊢ C → ε⊢ B → A ⊢ C
_b∘εr_ {C = C} f Bp w Ap =
  subst C
    (++-unit-r _)
    (f w [] Ap Bp)
