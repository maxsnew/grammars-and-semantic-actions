open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Reify.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.String.Base Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB : Level

module _ (P : String → Type ℓA) where
  Reify : Grammar ℓA
  Reify = ⊕[ w ∈ String ] ⊕[ x ∈ P w ] ⌈ w ⌉

  mkReify : {w : String} → (x : P w) → Reify w
  mkReify {w} x = w , x , mk⌈⌉ w

  readReify : ((w : String) → P w) → string ⊢ Reify
  readReify f w _ = mkReify (f w)

  module _ {B : Grammar ℓB} where
    elimReify : ((w : String) → (x : P w) → B w) → Reify ⊢ B
    elimReify f w x = subst B (⌈⌉→≡ (x .fst) w (x .snd .snd)) (f (x .fst) (x .snd .fst))
