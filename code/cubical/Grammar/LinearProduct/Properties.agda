open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearProduct.Base Alphabet

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g''' g'''' g''''' : Grammar ℓg
    h h' h'' h''' h'''' h''''' : Grammar ℓh
    f f' f'' f''' f'''' f''''' : g ⊢ h
    k : Grammar ℓk
    l : Grammar ℓl

open StrongEquivalence

module _
  {g : Grammar ℓg} {h : Grammar ℓh}
  {k : Grammar ℓk} {l : Grammar ℓl}
  (g≅h : g ≅ h)
  (k≅l : k ≅ l)
  where

  private
    the-fun : g ⊗ k ⊢ h ⊗ l
    the-fun = g≅h .fun ,⊗ k≅l .fun

    the-inv : h ⊗ l ⊢ g ⊗ k
    the-inv = g≅h .inv ,⊗ k≅l .inv
    opaque
      unfolding ⊗-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec i = g≅h .sec i ,⊗ k≅l .sec i

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret i = g≅h .ret i ,⊗ k≅l .ret i

  ⊗≅ : (g ⊗ k) ≅ (h ⊗ l)
  ⊗≅ .fun = the-fun
  ⊗≅ .inv = the-inv
  ⊗≅ .sec = the-sec
  ⊗≅ .ret = the-ret
