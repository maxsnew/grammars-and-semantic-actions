open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Equalizer.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet

open import Term.Base Alphabet

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
whichStringRetract : string isRetractOf (⊕[ w ∈ String ] ⌈ w ⌉)
whichStringRetract .weak .fun =
  fold*r char
    (σ [])
    (⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
     ∘g ⊕ᴰ-distR .fun)
whichStringRetract .weak .inv = ⊕ᴰ-elim ⌈⌉→string
whichStringRetract .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕ᴰ-distL ⊕ᴰ-distR
    the-ret : whichStringRetract .weak .inv ∘g whichStringRetract .weak .fun ≡ id
    the-ret =
      equalizer-ind (*Ty char) (λ _ → string) _ _
      (λ _ → ⊕ᴰ≡ _ _ λ where
        nil → refl
        cons i → CONS ∘g id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG
      )
      _

⊤→⊕⌈⌉ : ⊤ ⊢ ⊕[ w ∈ String ] ⌈ w ⌉
⊤→⊕⌈⌉ w _ = w , (mk⌈⌉ w)

⊤≅⊕⌈⌉ : ⊤ ≅ ⊕[ w ∈ String ] ⌈ w ⌉
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

unambiguous⊕⌈⌉ : unambiguous (⊕[ w ∈ String ] ⌈ w ⌉)
unambiguous⊕⌈⌉ = unambiguous≅ ⊤≅⊕⌈⌉ unambiguous⊤

unambiguous-string : unambiguous string
unambiguous-string = isUnambiguousRetract whichStringRetract unambiguous⊕⌈⌉
