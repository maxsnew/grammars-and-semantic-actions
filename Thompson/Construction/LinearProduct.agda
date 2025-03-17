{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module Thompson.Construction.LinearProduct (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

import      Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (init ; rec ; map)
open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.FinSet.More
import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)
open import Cubical.Data.SumFin using (Fin ; fzero ; isSetFin ; discreteFin)
open import Cubical.Data.Unit
import Cubical.HITs.PropositionalTruncation as PT hiding (rec)

open import Grammar Alphabet
open import Automata.NFA.Base Alphabet
open import Term Alphabet

open StrongEquivalence

private
  variable ℓN ℓN' ℓP ℓ : Level

open NFA
open NFA.Accepting

-- Concatenation
-- Given two NFAs N and N', accepts a string w if and only if
-- w ≡ w₁ ++ w₂ where w₁ is accepted by N and w₂ accepted by N'
module _ (N : NFA ℓN) (N' : NFA ℓN') where
  ⊗State : FinSet (ℓ-max ℓN ℓN')
  ⊗State .fst = ⟨ N .Q ⟩ Sum.⊎ ⟨ N' .Q ⟩
  ⊗State .snd = isFinSet⊎ (N .Q) (N' .Q)

  ⊗Trans : FinSet (ℓ-max ℓN ℓN')
  ⊗Trans .fst = ⟨ N .transition ⟩ Sum.⊎ ⟨ N' .transition ⟩
  ⊗Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊗εTrans : Type (ℓ-max ℓN ℓN') where
    N-acc : ∀ q → (true Eq.≡ N .isAcc q) → ⊗εTrans
    N-ε-trans  : ⟨ N .ε-transition ⟩ → ⊗εTrans
    N'-ε-trans  : ⟨ N' .ε-transition ⟩ → ⊗εTrans

  ⊗εTrans-rep :
    (Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q)) Sum.⊎
      (⟨ N .ε-transition ⟩ Sum.⊎ ⟨ N' .ε-transition ⟩)
      ≃ ⊗εTrans
  ⊗εTrans-rep = isoToEquiv (iso
    (λ { (Sum.inl (acc)) → N-acc _ (acc .snd)
       ; (Sum.inr (Sum.inl t)) → N-ε-trans t
       ; (Sum.inr (Sum.inr t')) → N'-ε-trans t'})
    (λ { (N-acc q acc) → Sum.inl (q , acc)
       ; (N-ε-trans t) → Sum.inr (Sum.inl t)
       ; (N'-ε-trans t') → Sum.inr (Sum.inr t') })
    (λ { (N-acc _ _) → refl
       ; (N-ε-trans _) → refl
       ; (N'-ε-trans _) → refl})
    (λ { (Sum.inl _) → refl
       ; (Sum.inr (Sum.inl _)) → refl
       ; (Sum.inr (Sum.inr _)) → refl }))

  ⊗NFA : NFA (ℓ-max ℓN ℓN')
  ⊗NFA .Q = ⊗State
  ⊗NFA .init = Sum.inl (N .init)
  ⊗NFA .isAcc = λ { (Sum.inl q) → false
                  ; (Sum.inr q') → N' .isAcc q' }
  ⊗NFA .transition = ⊗Trans
  ⊗NFA .src = λ { (Sum.inl t) → Sum.inl (N .src t) ; (Sum.inr t') → Sum.inr (N' .src t') }
  ⊗NFA .dst = λ { (Sum.inl t) → Sum.inl (N .dst t) ; (Sum.inr t') → Sum.inr (N' .dst t') }
  ⊗NFA .label = λ { (Sum.inl t) → N .label t ; (Sum.inr t') → N' .label t' }
  ⊗NFA .ε-transition .fst = ⊗εTrans
  ⊗NFA .ε-transition .snd =
    EquivPresIsFinSet ⊗εTrans-rep
      (isFinSet⊎
        ((_ , isFinSetΣ (N .Q)
          (λ q → _ , isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd))))
        (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
    where
      the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) (λ P → Dec (P .fst))
      the-dec-prop q =  isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  ⊗NFA .ε-src = λ { (N-acc q qAcc) → Sum.inl q
                  ; (N-ε-trans t) → Sum.inl (N .ε-src t)
                  ; (N'-ε-trans t') → Sum.inr (N' .ε-src t') }
  ⊗NFA .ε-dst = λ { (N-acc q qAcc) → Sum.inr (N' .init)
                  ; (N-ε-trans t) → Sum.inl (N .ε-dst t)
                  ; (N'-ε-trans t') → Sum.inr (N' .ε-dst t') }

  ⊗NFA≅ : Parse ⊗NFA ≅ Parse N ⊗ Parse N'
  ⊗NFA≅ =
    mkStrEq
      (rec _ ⊗Alg (⊗NFA .init))
      (N→⊗NFA (N .init))
      (the-retN (N .init))
      (the-secN (N .init))
    where
    ⟦_⟧⊗ : ⟨ ⊗NFA .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ Sum.inl q ⟧⊗ = Trace N q ⊗ Parse N'
    ⟦ Sum.inr q' ⟧⊗ = LiftG ℓN (Trace N' q')

    ⟦_⟧N : ⟨ N .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q ⟧N = Trace ⊗NFA (Sum.inr (N' .init)) ⊸ Trace ⊗NFA (Sum.inl q)

    ⟦_⟧N' : ⟨ N' .Q ⟩ → Grammar (ℓ-max ℓN ℓN')
    ⟦ q' ⟧N' = Trace ⊗NFA (Sum.inr q')

    ⊗Alg : Algebra (TraceTy ⊗NFA) ⟦_⟧⊗
    ⊗Alg (Sum.inl q) = ⊕ᴰ-elim (λ {
        (step (Sum.inl t) Eq.refl) →
          (STEP N t ,⊗ id
          ∘g ⊗-assoc)
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε (N-acc q acc) Eq.refl) →
          STOP N acc ,⊗ id
          ∘g ⊗-unit-l⁻
          ∘g lowerG ∘g lowerG
      ; (stepε (N-ε-trans t) Eq.refl) →
         STEPε N t ,⊗ id
         ∘g lowerG })
    ⊗Alg (Sum.inr q') = ⊕ᴰ-elim (λ {
        (stop acc) → liftG ∘g STOP N' acc ∘g lowerG ∘g lowerG
      ; (step (Sum.inr t) Eq.refl) →
        liftG ∘g STEP N' t
        ∘g (lowerG ∘g lowerG) ,⊗ (lowerG ∘g lowerG)
      ; (stepε (N'-ε-trans t) Eq.refl) →
        liftG ∘g STEPε N' t ∘g lowerG ∘g lowerG})

    N'Alg : Algebra (TraceTy N') ⟦_⟧N'
    N'Alg q =
      ⊕ᴰ-elim λ {
        (stop acc) → STOP ⊗NFA acc ∘g lowerG ∘g lowerG
      ; (step t Eq.refl) → STEP ⊗NFA (Sum.inr t) ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε t Eq.refl) → STEPε ⊗NFA (N'-ε-trans t) ∘g lowerG}

    NAlg : Algebra (TraceTy N) ⟦_⟧N
    NAlg q = ⊕ᴰ-elim λ {
         (stop acc) →
           ⊸-intro
             (STEPε ⊗NFA (N-acc q acc)
             ∘g ⊗-unit-l
             ∘g (lowerG ∘g lowerG) ,⊗ id)
       ; (step t Eq.refl) →
           ⊸-intro
             (STEP ⊗NFA (Sum.inl t)
             ∘g id ,⊗ ⊸-app
             ∘g ⊗-assoc⁻
             ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
       ; (stepε t Eq.refl) →
           ⊸-intro
             (STEPε ⊗NFA (N-ε-trans t)
             ∘g ⊸-app
             ∘g lowerG ,⊗ id)
       }

    N→⊗NFA : ∀ q → Trace N q ⊗ Parse N' ⊢ Trace ⊗NFA (Sum.inl q)
    N→⊗NFA q =
      ⊸-intro⁻ (rec (TraceTy N) NAlg q)
      ∘g id ,⊗ rec _ N'Alg (N' .init)

    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊕-elim eq-intro
      the-retN' : ∀ q' →
        lowerG ∘g rec _ ⊗Alg (Sum.inr q') ∘g rec _ N'Alg q' ≡ id
      the-retN' =
        equalizer-ind (TraceTy N') _ _ _
          (λ q' → ⊕ᴰ≡ _ _ λ {
            (stop acc) → refl
          ; (step t Eq.refl) → λ i →
            STEP N' t
            ∘g id ,⊗ eq-π-pf _ _ i
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          ; (stepε t Eq.refl) → λ i →
            STEPε N' t
            ∘g eq-π-pf _ _ i
            ∘g lowerG
          } )

      the-retN : ∀ q →
        rec _ ⊗Alg (Sum.inl q) ∘g N→⊗NFA q ≡ id
      the-retN q =
        equalizer-ind-⊗l
          (Tag N)
          _
          (λ q → Trace N q ⊗ Parse N')
          (λ _ → Parse N')
          (λ q → rec _ ⊗Alg (Sum.inl q) ∘g N→⊗NFA q)
          (λ q → id)
          (λ q → λ {
            (stop acc) →
              (λ i →
               rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl q)
               ∘g ⊸-β (STEPε ⊗NFA (N-acc q acc)
                       ∘g ⊗-unit-l
                       ∘g (lowerG ∘g lowerG) ,⊗ id) i
               ∘g id ,⊗ rec _ N'Alg (N' .init)
               ) ∙
              (λ i →
              STOP N acc ,⊗ id
              ∘g ⊗-unit-l⁻
              ∘g lowerG
              ∘g rec _ ⊗Alg (Sum.inr (N' .init))
              ∘g ⊗-unit-l⊗-intro (rec _ N'Alg (N' .init)) (~ i)
              ∘g (lowerG ∘g lowerG) ,⊗ id
             ) ∙
            (λ i →
              STOP N acc ,⊗ id
              ∘g ⊗-unit-l⁻
              ∘g the-retN' (N' .init) i
              ∘g ⊗-unit-l
              ∘g (lowerG ∘g lowerG) ,⊗ id
             ) ∙
             (λ i →
               STOP N acc ,⊗ id
                ∘g ⊗-unit-ll⁻ i
                ∘g (lowerG ∘g lowerG) ,⊗ id
               )
          ; (step t Eq.refl) →
            (λ i →
              rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .src t))
              ∘g ⊸-β
                (STEP ⊗NFA (Sum.inl t)
                ∘g id ,⊗ ⊸-app
                ∘g ⊗-assoc⁻
                ∘g ((lowerG ∘g lowerG {ℓB = ℓ-max ℓN ℓN'}) ,⊗ lowerG {ℓB = ℓN}) ,⊗ id)
                i
              ∘g ((liftG ∘g liftG {ℓB = ℓN}) ,⊗ (liftG ∘g rec (TraceTy N) NAlg (N .dst t))) ,⊗ id
              ∘g (id ,⊗ eq-π _ _ ∘g (lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
              ∘g id ,⊗ rec _ N'Alg (N' .init)
            ) ∙
            (λ i →
            STEP N t ,⊗ id
            ∘g ⊗-assoc
            ∘g id ,⊗ eq-π-pf-⊸-intro (rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t)) ∘g N→⊗NFA (N .dst t)) id i
            ∘g ⊗-assoc⁻
            ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id) ∙
            (λ i →
               STEP N t ,⊗ id
               ∘g ⊗-assoc∘⊗-assoc⁻≡id i
               ∘g (id ,⊗ eq-π _ _) ,⊗ id
               ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
            )
          ; (stepε t Eq.refl) →
              (λ i →
                rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .ε-src t))
                ∘g ⊸-β
                    (STEPε ⊗NFA (N-ε-trans t)
                      ∘g ⊸-app
                      ∘g lowerG {ℓB = ℓN} ,⊗ id)
                   i
                ∘g (liftG ∘g rec (TraceTy N) NAlg (N .ε-dst t)) ,⊗ id
                ∘g (eq-π _ _ ∘g lowerG) ,⊗ id
                ∘g id ,⊗ rec _ N'Alg (N' .init)
              ) ∙
              (λ i →
                STEPε N t ,⊗ id
                ∘g eq-π-pf-⊸-intro (rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .ε-dst t)) ∘g N→⊗NFA (N .ε-dst t)) id i
                ∘g lowerG ,⊗ id
              )
          })
          q

      -- Annoying artifact of how equalizer-induction is written:
      -- Need to handle each of the ⊗NFA states, even if the Sum.inl
      -- half of this proof is unecessary
      -- To handle this, map the Sum.inl terms to ⊤* so the
      -- equations are trivial to prove
      the-secN' : ∀ q' →
        rec _ N'Alg q' ∘g lowerG ∘g rec _ ⊗Alg (Sum.inr q') ≡ id
      the-secN' q' =
        equalizer-ind
          (TraceTy ⊗NFA)
          (λ {
            (Sum.inl q) → ⊤*
          ; (Sum.inr q') → Trace ⊗NFA (Sum.inr q')})
          (λ {
            (Sum.inl q) → ⊤*-intro
          ; (Sum.inr q') → rec _ N'Alg q' ∘g lowerG ∘g rec _ ⊗Alg (Sum.inr q')})
          (λ {
            (Sum.inl q) → ⊤*-intro
          ; (Sum.inr q') → id})
          (λ {
            (Sum.inl q) → unambiguous⊤* _ _
          ; (Sum.inr q') →
              ⊕ᴰ≡ _ _ λ {
                  (stop acc) → refl
              ; (step (Sum.inr t) Eq.refl) → λ i →
                  STEP ⊗NFA (Sum.inr t) ∘g id ,⊗ eq-π-pf _ _ i ∘g (lowerG ∘g lowerG) ,⊗ lowerG
              ; (stepε (N'-ε-trans t) Eq.refl) → λ i →
                  STEPε ⊗NFA (N'-ε-trans t) ∘g eq-π-pf _ _ i ∘g lowerG
              }
          })
          (Sum.inr q')

      the-secN : ∀ q →
        N→⊗NFA q ∘g rec _ ⊗Alg (Sum.inl q) ≡ id
      the-secN q =
        equalizer-ind
          (TraceTy ⊗NFA)
          (λ {
            (Sum.inl q) → Trace ⊗NFA (Sum.inl q)
          ; (Sum.inr q') → ⊤*
          })
          (λ {
            (Sum.inl q) → N→⊗NFA q ∘g rec _ ⊗Alg (Sum.inl q)
          ; (Sum.inr q') → ⊤*-intro
          })
          (λ {
            (Sum.inl q) → id
          ; (Sum.inr q') → ⊤*-intro
          })
          (λ {
            (Sum.inl q) →
              ⊕ᴰ≡ _ _
                λ {
                  (step (Sum.inl t) Eq.refl) →
                    (
                    ⊸-intro⁻ (⊸-intro
                        (STEP ⊗NFA (Sum.inl t)
                        ∘g id ,⊗ ⊸-app
                        ∘g ⊗-assoc⁻
                        ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id))
                    ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
                    ∘g (id ,⊗ rec (TraceTy N) NAlg (N .dst t)) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g ⊗-assoc
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                          ⊸-β
                            (STEP ⊗NFA (Sum.inl t)
                              ∘g id ,⊗ ⊸-app
                              ∘g ⊗-assoc⁻
                              ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id) i
                          ∘g ((liftG {ℓB = ℓ-max ℓN ℓN'}
                                ∘g liftG {ℓB = ℓN}) ,⊗ liftG {ℓB = ℓN}) ,⊗ id
                          ∘g (id ,⊗ rec (TraceTy N) NAlg (N .dst t)) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g ⊗-assoc
                          ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t))
                          ∘g id ,⊗ eq-π _ _
                          ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                        )
                      ⟩
                    STEP ⊗NFA (Sum.inl t)
                    ∘g id ,⊗ ⊸-app
                    ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                    ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                    ∘g ⊗-assoc⁻
                    ∘g ⊗-assoc
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                         STEP ⊗NFA (Sum.inl t)
                         ∘g id ,⊗ ⊸-app
                         ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                         ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                         ∘g ⊗-assoc⁻∘⊗-assoc≡id i
                         ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t))
                         ∘g id ,⊗ eq-π _ _
                         ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                         )
                      ⟩
                    STEP ⊗NFA (Sum.inl t)
                    ∘g id ,⊗ ⊸-app
                    ∘g id ,⊗ (rec (TraceTy N) NAlg (N .dst t) ,⊗ id)
                    ∘g id ,⊗ (id ,⊗ rec _ N'Alg (N' .init))
                    ∘g id ,⊗ rec (TraceTy ⊗NFA) ⊗Alg (Sum.inl (N .dst t))
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                      ≡⟨ (λ i →
                          STEP ⊗NFA (Sum.inl t)
                          ∘g id ,⊗ eq-π-pf _ _ i
                          ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                         )
                      ⟩
                    STEP ⊗NFA (Sum.inl t)
                    ∘g id ,⊗ eq-π _ _
                    ∘g (lowerG ∘g lowerG) ,⊗ (lowerG)
                    ∎
                    )
                ; (stepε (N-ε-trans t) Eq.refl) →
                    (
                    ⊸-intro⁻ (⊸-intro
                         (STEPε ⊗NFA (N-ε-trans t)
                         ∘g ⊸-app
                         ∘g lowerG ,⊗ id))
                    ∘g liftG ,⊗ id
                    ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g rec _ ⊗Alg (Sum.inl (N .ε-dst t))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          ⊸-β
                            (STEPε ⊗NFA (N-ε-trans t)
                            ∘g ⊸-app
                            ∘g lowerG {ℓB = ℓN} ,⊗ id)
                            i
                          ∘g liftG ,⊗ id
                          ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g rec _ ⊗Alg (Sum.inl (N .ε-dst t))
                          ∘g eq-π _ _
                          ∘g lowerG
                          )
                      ⟩
                    STEPε ⊗NFA (N-ε-trans t)
                    ∘g ⊸-app
                    ∘g rec (TraceTy N) NAlg (N .ε-dst t) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g rec _ ⊗Alg (Sum.inl (N .ε-dst t))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨  (λ i →
                          STEPε ⊗NFA (N-ε-trans t)
                          ∘g eq-π-pf _ _ i
                          ∘g lowerG
                          )
                      ⟩
                    STEPε ⊗NFA (N-ε-trans t)
                    ∘g eq-π _ _
                    ∘g lowerG
                    ∎
                    )
                ; (stepε (N-acc q acc) Eq.refl) →
                    (
                    ⊸-app
                    ∘g ⊸-intro
                        (STEPε ⊗NFA (N-acc q acc)
                        ∘g ⊗-unit-l
                        ∘g (lowerG ∘g lowerG) ,⊗ id) ,⊗ id
                    ∘g (liftG ∘g liftG) ,⊗ id
                    ∘g id ,⊗ rec _ N'Alg (N' .init)
                    ∘g ⊗-unit-l⁻
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (Sum.inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          ⊸-β
                          (STEPε ⊗NFA (N-acc q acc)
                            ∘g ⊗-unit-l
                            ∘g (lowerG {ℓB = ℓN}
                                  ∘g lowerG {ℓB = ℓ-max ℓN ℓN'}) ,⊗ id) i
                          ∘g (liftG ∘g liftG) ,⊗ id
                          ∘g id ,⊗ rec _ N'Alg (N' .init)
                          ∘g ⊗-unit-l⁻
                          ∘g lowerG
                          ∘g rec _ ⊗Alg (Sum.inr (N' .init))
                          ∘g eq-π _ _
                          ∘g lowerG
                        )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g ⊗-unit-l
                    ∘g ⊗-unit-l⁻
                    ∘g rec _ N'Alg (N' .init)
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (Sum.inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨ (λ i →
                          STEPε ⊗NFA (N-acc q acc)
                          ∘g ⊗-unit-l⁻l i
                          ∘g rec _ N'Alg (N' .init)
                          ∘g lowerG
                          ∘g rec _ ⊗Alg (Sum.inr (N' .init))
                          ∘g eq-π _ _
                          ∘g lowerG
                         )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g rec _ N'Alg (N' .init)
                    ∘g lowerG
                    ∘g rec _ ⊗Alg (Sum.inr (N' .init))
                    ∘g eq-π _ _
                    ∘g lowerG
                      ≡⟨
                        (λ i →
                          STEPε ⊗NFA (N-acc q acc)
                          ∘g the-secN' (N' .init) i
                          ∘g eq-π _ _
                          ∘g lowerG
                        )
                      ⟩
                    STEPε ⊗NFA (N-acc q acc)
                    ∘g eq-π _ _
                    ∘g lowerG
                    ∎
                    )
                }
          ; (Sum.inr q') → unambiguous⊤* _ _
          })
          (Sum.inl q)
