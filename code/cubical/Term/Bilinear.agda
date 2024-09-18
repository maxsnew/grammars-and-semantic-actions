open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Bilinear (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Grammar.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{-- A direct interpretation of terms of 2 variables
 -- x : g , y : h ⊢ M : k
 --
 --}
Bilinear : Grammar ℓg → Grammar ℓh → Grammar ℓk → Type _
Bilinear g h k = ∀ w1 w2 → g w1 → h w2 → k (w1 ++ w2)

_,,_⊢_ : Grammar ℓg → Grammar ℓh → Grammar ℓk → Type _
_,,_⊢_ = Bilinear

_∘b_ : k ⊢ l → g ,, h ⊢ k → g ,, h ⊢ l
_∘b_ f f' = λ w1 w2 gp hp → f (w1 ++ w2) (f' w1 w2 gp hp)

_b∘l_ : g ,, h ⊢ k → l ⊢ g → l ,, h ⊢ k
(f b∘l f') w1 w2 lp hp = f w1 w2 (f' w1 lp) hp

_b∘r_ : g ,, h ⊢ k → l ⊢ h → g ,, l ⊢ k
(f b∘r f') w1 w2 gp lp = f w1 w2 gp (f' w2 lp)

-- Does the fact that this is refl make anything easier?
-- TODO: should these be opaque?
_b∘εl_ : g ,, h ⊢ k → ε⊢ g → h ⊢ k
_b∘εl_ {k = k} f gp w hp =
   (f [] w gp hp)

_b∘εr_ : g ,, h ⊢ k → ε⊢ h → g ⊢ k
_b∘εr_ {k = k} f hp w gp =
  subst k
    (++-unit-r _)
    (f w [] gp hp)

