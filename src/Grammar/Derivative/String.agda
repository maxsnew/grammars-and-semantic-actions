open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Derivative.String (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Top Alphabet
open import Grammar.String Alphabet
open import Grammar.Derivative.Base Alphabet
open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- String-indexed Brzozowski derivatives.
Dr-string : String → Grammar ℓA → Grammar ℓA
Dr-string w A = ⌈ w ⌉ ⊸ A

Dl-string : Grammar ℓA → String → Grammar ℓA
Dl-string A w = A ⟜ ⌈ w ⌉

√l-string : String → Grammar ℓA → Grammar ℓA
√l-string w A = (⌈ w ⌉ ⊗ ⊤) ⇒ (⌈ w ⌉ ⊗ A)

√r-string : String → Grammar ℓA → Grammar ℓA
√r-string w A = (⊤ ⊗ ⌈ w ⌉) ⇒ (A ⊗ ⌈ w ⌉)

opaque
  unfolding _⟜_ _⇒_ _⊗_ ⊤
  √l-string-app : Dl-string (√l-string w A) w ⊢ A
  √l-string-app {w = w} {A = A} w' d =
    Eq.transport A uniq-suffix (step .snd .snd)
    where
      step : (⌈ w ⌉ ⊗ A) (w ++ w')
      step = d w (mk⌈⌉ w) (((w , w') , Eq.refl) , (mk⌈⌉ w , _))

      uniq-suffix : step .fst .fst .snd Eq.≡ w'
      uniq-suffix =
        ++-cancelˡEq w
          (Eq.sym
            (Eq.transport (λ ww → w ++ w' Eq.≡ ww ++ step .fst .fst .snd)
                          (Eq.sym (uniquely-supported-⌈⌉Eq w (step .fst .fst .fst)
                                    (step .snd .fst)))
                          (step .fst .snd)))

  √r-string-app : Dr-string w (√r-string w A) ⊢ A
  √r-string-app {w = w} {A = A} w' d =
    Eq.transport A uniq-prefix (step .snd .fst)
    where
      step : (A ⊗ ⌈ w ⌉) (w' ++ w)
      step = d w (mk⌈⌉ w) (((w' , w) , Eq.refl) , (_ , mk⌈⌉ w))

      uniq-prefix : step .fst .fst .fst Eq.≡ w'
      uniq-prefix =
        ++-cancelʳEq w
          (Eq.sym
            (Eq.transport (λ ww → w' ++ w Eq.≡ step .fst .fst .fst ++ ww)
                          (Eq.sym (uniquely-supported-⌈⌉Eq w (step .fst .fst .snd)
                                    (step .snd .snd)))
                          (step .fst .snd)))
