{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Unambiguous (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Top Alphabet isSetAlphabet
open import Grammar.Sum Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Grammar.Equalizer.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive Alphabet isSetAlphabet
open import Grammar.String.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet

open import Term.Base Alphabet isSetAlphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

open _isRetractOf_
open WeakEquivalence
@0 whichStringRetract : string isRetractOf (⊕[ w ∈ String ] ⌈ w ⌉)
whichStringRetract .weak .fun =
  fold*r char
    (σ [])
    (⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distLEq .fun)
     ∘g ⊕ᴰ-distREq .fun)
whichStringRetract .weak .inv = ⊕ᴰ-elim ⌈⌉→string
whichStringRetract .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕ᴰ-distL ⊕ᴰ-distR
    the-ret : whichStringRetract .weak .inv ∘g whichStringRetract .weak .fun ≡ id
    the-ret =
      equalizer-ind (*Ty char) (λ _ → string) _ _
      (λ _ → ⊕ᴰ≡ _ _ λ @0 where
        nil → refl
        cons i → CONS ∘g id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG
      )
      _

@0 ⊤→⊕⌈⌉ : ⊤ ⊢ ⊕[ w ∈ String ] ⌈ w ⌉
⊤→⊕⌈⌉ w _ = w , (mk⌈⌉ w)

@0 ⊤≅⊕⌈⌉ : ⊤ ≅ ⊕[ w ∈ String ] ⌈ w ⌉
⊤≅⊕⌈⌉ .fun = ⊤→⊕⌈⌉
⊤≅⊕⌈⌉ .inv = ⊤-intro
⊤≅⊕⌈⌉ .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕ᴰ-distL ⊕ᴰ-distR mk⌈⌉
    the-sec : ⊤→⊕⌈⌉ ∘g ⊤-intro ≡ id
    the-sec = ⊕ᴰ≡ _ _ λ w →
      funExt λ w' → funExt λ p →
        Σ≡Prop (λ w'' → isLang⌈⌉ w'' w') (sym (⌈⌉→≡ w w' p))
⊤≅⊕⌈⌉ .ret = unambiguous⊤ _ _

@0 unambiguous⊕⌈⌉ : unambiguous (⊕[ w ∈ String ] ⌈ w ⌉)
unambiguous⊕⌈⌉ = unambiguous≅ ⊤≅⊕⌈⌉ unambiguous⊤

@0 unambiguous-string : unambiguous string
unambiguous-string = isUnambiguousRetract whichStringRetract unambiguous⊕⌈⌉
