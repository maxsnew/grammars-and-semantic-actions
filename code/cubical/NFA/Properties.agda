open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

open import NFA.Base Alphabet
open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet
open import Helper

open StrongEquivalence

private
  variable
    ℓN : Level

module _ (N : NFA ℓN) where
  open NFA N
  private
    module Acc = NFA.Accepting N
    module PR = NFA.PotentiallyRejecting N

  AccAlg : Acc.TraceAlg (PR.Trace true)
  AccAlg q = ⊕ᴰ-elim λ {
      (Acc.stop x) →
        roll ∘g ⊕ᴰ-in PR.stop ∘g ⊕ᴰ-in (lift x)
    ; (Acc.step t Eq.refl) →
       roll ∘g ⊕ᴰ-in PR.step ∘g ⊕ᴰ-in (t , Eq.refl)
    ; (Acc.stepε t Eq.refl) →
       roll ∘g ⊕ᴰ-in PR.stepε ∘g ⊕ᴰ-in (t , Eq.refl)
    }

  PRAlg : PR.TraceAlg true Acc.Trace
  PRAlg q = ⊕ᴰ-elim λ {
      (PR.stop) →
         roll ∘g ⊕ᴰ-elim λ {
           (lift (acc)) →
             ⊕ᴰ-in (Acc.stop acc)
         }
    ; (PR.step) →
         roll ∘g ⊕ᴰ-elim λ {
           (t , Eq.refl) → ⊕ᴰ-in (Acc.step t Eq.refl)
         }
    ; (PR.stepε) →
         roll ∘g ⊕ᴰ-elim λ {
           (t , Eq.refl) → ⊕ᴰ-in (Acc.stepε t Eq.refl)
         }
    }

  Trace≅ : ∀ (q : ⟨ Q ⟩) → Acc.Trace q ≅ PR.Trace true q
  Trace≅ q .fun = rec _ AccAlg q
  Trace≅ q .inv = rec _ PRAlg q
  Trace≅ q .sec = the-sec
    where
    opaque
      unfolding ⊗-intro eq-intro ⊗-unit-r⁻
      the-sec : rec Acc.TraceTy AccAlg q ∘g rec (PR.TraceTy true) PRAlg q ≡ id
      the-sec = 
        equalizer-ind
          (PR.TraceTy true)
          (PR.Trace true)
          (λ q → rec _ AccAlg q ∘g rec _ PRAlg q)
          (λ _ → id)
          (λ q →
            ⊕ᴰ≡ _ _
              λ {
              PR.stop → refl
            ; PR.step → ⊕ᴰ≡ _ _ λ {
              (t , Eq.refl) →
                roll
                ∘g ⊕ᴰ-in PR.step
                ∘g ⊕ᴰ-in (t , Eq.refl)
                ∘g (liftG ∘g liftG) ,⊗ liftG
                ∘g id ,⊗ rec Acc.TraceTy AccAlg (dst t)
                ∘g id ,⊗ rec (PR.TraceTy true) PRAlg (dst t)
                ∘g id ,⊗ eq-π _ _
                ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                  ≡⟨
                    (λ i →
                       roll
                       ∘g ⊕ᴰ-in PR.step
                       ∘g ⊕ᴰ-in (t , Eq.refl)
                       ∘g (liftG ∘g liftG) ,⊗ liftG
                       ∘g id ,⊗ eq-π-pf _ _ i
                       ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                    )
                  ⟩
                roll
                ∘g ⊕ᴰ-in PR.Tag.step
                ∘g ⊕ᴰ-in (t , Eq.refl)
                ∘g id ,⊗ liftG
                ∘g id ,⊗ eq-π _ _ 
                ∘g id ,⊗ lowerG
                ∎
            }
            ; PR.stepε → ⊕ᴰ≡ _ _ λ {
            (t , Eq.refl) → λ i →
              roll
              ∘g ⊕ᴰ-in PR.stepε
              ∘g ⊕ᴰ-in (t , Eq.refl)
              ∘g liftG
              ∘g eq-π-pf _ _ i
              ∘g lowerG
            }
            }
          )
          q
  Trace≅ q .ret = the-ret
    where
    opaque
      unfolding ⊗-intro eq-intro ⊗-unit-r⁻
      the-ret :
        rec (PR.TraceTy true) PRAlg q
        ∘g rec Acc.TraceTy AccAlg q
        ≡
        id
      the-ret = equalizer-ind
          Acc.TraceTy
          Acc.Trace
          (λ q → rec _ PRAlg q ∘g rec _ AccAlg q)
          (λ _ → id)
          (λ q →
            ⊕ᴰ≡ _ _
              λ {
              (Acc.stop acc) → refl
            ; (Acc.step t Eq.refl) → λ i →
              Acc.STEP t
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            ; (Acc.stepε t Eq.refl) → λ i →
              Acc.STEPε t
              ∘g eq-π-pf _ _ i
              ∘g lowerG
            }
          )
          q
