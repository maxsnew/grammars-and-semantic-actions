{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Top Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet

open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

-- oh no this won't work either
module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  unambiguous-string : unambiguous string
  unambiguous-string =
    unambiguous≅
      (sym-strong-equivalence (*≅ε⊕g⊗g* char))
      (unambiguous⊕
        disjoint-ε-char+
        (unambiguousε isFinSetAlphabet)
        {!!}
        isFinSetAlphabet
      )


⊤→string : ⊤ ⊢ string
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤→string' : ⊤ ⊢ string
⊤→string' w _ = mkstring' w

⊤*→string : ∀ {ℓg} → ⊤* {ℓg} ⊢ string
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

string-intro : ∀ {ℓg} {g : Grammar ℓg} → g ⊢ string
string-intro = ⊤→string ∘g ⊤-intro

open StrongEquivalence
string≅⊤ : StrongEquivalence string ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = ⊤→string'
string≅⊤ .sec = unambiguous⊤ _ _
string≅⊤ .ret = the-ret
  where
  opaque
    unfolding ⊗-in ε-intro lit-intro
    the-ret : ⊤→string' ∘g ⊤-intro ≡ id
    the-ret = funExt λ {
        [] → funExt λ {
          (roll .[] (nil , (lift (lift x)))) →
            λ i → roll [] (nil , lift (lift {!!}))
        ; (roll .[] (cons , (s , x , y))) → {!!}
          }
      ; (c ∷ w) → {!!}
      }
      -- equalizer-ind
      -- _
      -- _
      -- _
      -- _
      -- (λ _ → ⊕ᴰ≡ _ _
      --   λ {
      --   nil → {!!}
      -- ; cons → {!!}
      -- }
      -- )
      -- _
