{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

module Grammar.String.Unambiguous (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.MonoidalStructure.Base Alphabet isSetAlphabet
open import Grammar.Top Alphabet isSetAlphabet
open import Grammar.Sum Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Grammar.Equalizer.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet isSetAlphabet
open import Grammar.Inductive.Indexed Alphabet isSetAlphabet as Ind
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

module _ {{monStr : MonoidalStr}} where
  open MonoidalStr monStr
  whichStringRetract : string isRetractOf (⊕[ w ∈ String ] ⌈ w ⌉)
  whichStringRetract .weak .fun = string→⌈⌉
  whichStringRetract .weak .inv = ⊕ᴰ-elim ⌈⌉→string
  whichStringRetract .ret = the-ret
    where
    the-ret : whichStringRetract .weak .inv ∘g whichStringRetract .weak .fun ≡ id
    the-ret =
      equalizer-ind (*Ty char) (λ _ → string) _ _
      (λ _ → ⊕ᴰ≡ _ _ λ @0 where
        nil → refl
        cons →
          ⊕ᴰ-elim (λ c →
            roll ∘g σ cons ∘g liftG ,⊗ liftG
            ∘g ⊕ᴰ-elim (λ w → σ c ,⊗ ⌈⌉→string w)
            ∘g ⊕ᴰ-distR .fun
          )
          ∘g ⊕ᴰ-distL .fun
          ∘g lowerG ,⊗ lowerG
          ∘g id ,⊗ mapLiftG string→⌈⌉
          ∘g id ,⊗ mapLiftG (eq-π _ _)
            ≡⟨ (λ i →
                  ⊕ᴰ-elim (λ c →
                    roll ∘g σ cons ∘g liftG ,⊗ liftG
                    ∘g ⊕ᴰ-distR-β' {X = String} ⌈⌉→string (σ c) i
                  )
                  ∘g ⊕ᴰ-distL .fun
                  ∘g lowerG ,⊗ (lowerG {ℓB = ℓ-zero})
                  ∘g id ,⊗ mapLiftG string→⌈⌉
                  ∘g id ,⊗ mapLiftG {ℓD = ℓ-zero} (eq-π _ _)
               ) ⟩
          roll ∘g σ cons ∘g liftG ,⊗ liftG
          ∘g ⊕ᴰ-elim (λ c → σ c ,⊗ ⊕ᴰ-elim ⌈⌉→string)
          ∘g ⊕ᴰ-distL .fun
          ∘g lowerG ,⊗ lowerG
          ∘g id ,⊗ mapLiftG string→⌈⌉
          ∘g id ,⊗ mapLiftG (eq-π _ _)
            ≡⟨ (λ i →
                  roll ∘g σ cons ∘g liftG ,⊗ liftG
                  ∘g ⊕ᴰ-distL-β' (λ c → σ c) (⊕ᴰ-elim ⌈⌉→string) i
                  ∘g lowerG ,⊗ (lowerG {ℓB = ℓ-zero})
                  ∘g id ,⊗ mapLiftG string→⌈⌉
                  ∘g id ,⊗ mapLiftG {ℓD = ℓ-zero} (eq-π _ _)
               ) ⟩
          roll ∘g σ cons ∘g liftG ,⊗ liftG
          ∘g id ,⊗ ⊕ᴰ-elim ⌈⌉→string
          ∘g lowerG ,⊗ lowerG
          ∘g id ,⊗ mapLiftG string→⌈⌉
          ∘g id ,⊗ mapLiftG (eq-π _ _)
            ≡⟨ (λ i →
                 roll ∘g σ cons
                 ∘g ⊗-intro∘g⊗-intro {f = id} {f' = ⊕ᴰ-elim ⌈⌉→string} {f'' = liftG} {f''' = liftG} i
                 ∘g lowerG ,⊗ (lowerG {ℓB = ℓ-zero})
                 ∘g ⊗-intro∘g⊗-intro {f = id} {f' = mapLiftG {ℓD = ℓ-zero} (eq-π _ _)}
                                     {f'' = id} {f''' = mapLiftG string→⌈⌉} i
               ) ⟩
          roll ∘g σ cons
          ∘g liftG ,⊗ (liftG ∘g ⊕ᴰ-elim ⌈⌉→string)
          ∘g lowerG ,⊗ lowerG
          ∘g id ,⊗ mapLiftG (string→⌈⌉ ∘g eq-π _ _)
            ≡⟨ (λ i →
                 roll ∘g σ cons
                 ∘g ⊗-intro∘g⊗-intro {D = ⊕[ w ∈ String ] ⌈ w ⌉}
                                     {f = lowerG {ℓB = ℓ-zero}} {f' = lowerG {ℓB = ℓ-zero}}
                                     {f'' = liftG} {f''' = liftG ∘g ⊕ᴰ-elim ⌈⌉→string} i
                 ∘g id ,⊗ mapLiftG {ℓD = ℓ-zero} (string→⌈⌉ ∘g eq-π _ _)
               ) ⟩
          roll ∘g σ cons
          ∘g id ,⊗ mapLiftG (⊕ᴰ-elim ⌈⌉→string)
          ∘g id ,⊗ mapLiftG (string→⌈⌉ ∘g eq-π _ _)
            ≡⟨ (λ i →
                 roll ∘g σ cons
                 ∘g ⊗-intro∘g⊗-intro {D = LiftG ℓ-zero (⊕[ w ∈ String ] ⌈ w ⌉)}
                                     {f = id} {f' = mapLiftG (string→⌈⌉ ∘g eq-π _ _)}
                                     {f'' = id} {f''' = mapLiftG (⊕ᴰ-elim ⌈⌉→string)} i
               ) ⟩
          roll ∘g σ cons ∘g id ,⊗ mapLiftG (⊕ᴰ-elim ⌈⌉→string ∘g string→⌈⌉ ∘g eq-π _ _)
            ≡⟨ (λ i → roll ∘g σ cons ∘g id ,⊗ mapLiftG (eq-π-pf _ _ i)) ⟩
          roll ∘g σ cons ∘g id ,⊗ mapLiftG (eq-π _ _)
          ∎
      )
      _

  ⊤→⊕⌈⌉ : ⊤ ⊢ ⊕[ w ∈ String ] ⌈ w ⌉
  ⊤→⊕⌈⌉ w _ = w , (mk⌈⌉ w)

  module _ (isLang⌈⌉ : ∀ w → isLang ⌈ w ⌉) (⌈⌉→≡ : ∀ w w' → ⌈ w ⌉ w' → w ≡ w')
    where
    @0 ⊤≅⊕⌈⌉ : ⊤ ≅ ⊕[ w ∈ String ] ⌈ w ⌉
    ⊤≅⊕⌈⌉ .fun = ⊤→⊕⌈⌉
    ⊤≅⊕⌈⌉ .inv = ⊤-intro
    ⊤≅⊕⌈⌉ .sec = the-sec
      where
      the-sec : ⊤→⊕⌈⌉ ∘g ⊤-intro ≡ id
      the-sec =
        ⊕ᴰ≡ _ _ λ w → funExt λ w' → funExt λ p →
          Σ≡Prop (λ w'' → isLang⌈⌉ w'' w') (sym (⌈⌉→≡ w w' p))
    ⊤≅⊕⌈⌉ .ret = unambiguous⊤ _ _

    @0 unambiguous⊕⌈⌉ : unambiguous (⊕[ w ∈ String ] ⌈ w ⌉)
    unambiguous⊕⌈⌉ = unambiguous≅ ⊤≅⊕⌈⌉ unambiguous⊤

    @0 unambiguous-string : unambiguous string
    unambiguous-string = isUnambiguousRetract whichStringRetract unambiguous⊕⌈⌉
