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

whichString≅ : string ≅ (⊕[ w ∈ String ] ⌈ w ⌉)
whichString≅ .fun =
  fold*r char
    (σ [])
    (⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
     ∘g ⊕ᴰ-distR .fun)
whichString≅ .inv = ⊕ᴰ-elim ⌈⌉→string
whichString≅ .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL

    help : (w : String) → whichString≅ .fun ∘g ⌈⌉→string w ≡ σ w
    help [] = refl
    help (c ∷ w) =
        (⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
        ∘g ⊕ᴰ-distR .fun)
        ∘g id ,⊗ whichString≅ .fun
        ∘g σ c ,⊗ ⌈⌉→string w
            ≡⟨ refl ⟩
        ⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
        ∘g ⊕ᴰ-distR .fun
        ∘g σ c ,⊗ id
        ∘g id ,⊗ whichString≅ .fun
        ∘g id ,⊗ ⌈⌉→string w
            ≡⟨ (λ i →
                ⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
                ∘g ⊕ᴰ-distR .fun
                ∘g σ c ,⊗ id
                ∘g id ,⊗ help w i
            ) ⟩
        ⊕ᴰ-elim (λ w → (⊕ᴰ-elim λ c → σ (c ∷ w)) ∘g ⊕ᴰ-distL .fun)
        ∘g ⊕ᴰ-distR .fun
        ∘g σ c ,⊗ id
        ∘g id ,⊗ σ w
            ≡⟨ refl ⟩
        σ (c ∷ w)
        ∎

    the-sec : whichString≅ .fun ∘g ⊕ᴰ-elim ⌈⌉→string ≡ id
    the-sec = ⊕ᴰ≡ _ _ help

whichString≅ .ret = the-ret
  where
  opaque
      unfolding ⊗-intro ⊕ᴰ-distL ⊕ᴰ-distR
      the-ret : whichString≅ .inv ∘g whichString≅ .fun ≡ id
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
unambiguous-string = unambiguous≅ (sym≅ whichString≅) unambiguous⊕⌈⌉
