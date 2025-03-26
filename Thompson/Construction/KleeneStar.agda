{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

module Thompson.Construction.KleeneStar (Alphabet : hSet ℓ-zero) where

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

-- Kleene Star
module _ (N : NFA ℓN) where
  data *εTrans : Type ℓN where
    inr' : *εTrans
    cons⟨N⟩ : ∀ {q} → true Eq.≡ N .isAcc q  → *εTrans
    N-internal : ⟨ N .ε-transition ⟩ → *εTrans

  *εTrans-rep :
    (Unit Sum.⊎ ((Σ[ q ∈ _ ] (true Eq.≡ N .isAcc q)) Sum.⊎ ⟨ N .ε-transition ⟩)) ≃ *εTrans
  *εTrans-rep = isoToEquiv
    (iso
      (λ { (Sum.inl x) → inr'
         ; (Sum.inr (Sum.inl x)) → cons⟨N⟩ (x .snd)
         ; (Sum.inr (Sum.inr x)) → N-internal x })
      (λ { inr' → Sum.inl tt
         ; (cons⟨N⟩ x) → Sum.inr (Sum.inl (_ , x))
         ; (N-internal x) → Sum.inr (Sum.inr x)})
      (λ { inr' → refl ; (cons⟨N⟩ x) → refl ; (N-internal x) → refl })
      λ { (Sum.inl x) → refl ; (Sum.inr (Sum.inl x)) → refl ; (Sum.inr (Sum.inr x)) → refl })

  *NFA : NFA ℓN
  *NFA .Q = Unit Sum.⊎ N .Q .fst , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
  *NFA .init = Sum.inl _
  *NFA .isAcc (Sum.inl _) = true
  *NFA .isAcc (Sum.inr q) = false
  *NFA .transition = N .transition
  *NFA .src = Sum.inr ∘ N .src
  *NFA .dst = Sum.inr ∘ N .dst
  *NFA .label = N .label
  *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (_ ,
      isFinSetΣ (N .Q) (λ q → _ ,
       isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd)
       )) (N .ε-transition)))
    where
      the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) (λ P → Dec (P .fst))
      the-dec-prop q =  isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  *NFA .ε-src inr' = Sum.inl _
  *NFA .ε-dst inr' = Sum.inr (N .init)
  *NFA .ε-src (cons⟨N⟩ {q} _) = Sum.inr q
  *NFA .ε-dst (cons⟨N⟩ {q} _) = Sum.inl _
  *NFA .ε-src (N-internal t) = Sum.inr (N .ε-src t)
  *NFA .ε-dst (N-internal t) = Sum.inr (N .ε-dst t)

  *NFA≅ : Parse *NFA ≅ Parse N *
  *NFA≅ =
    mkStrEq
      (from*NFA (Sum.inl _))
      (to*NFA (Sum.inl _))
      (ind-id'
        (*Ty (Parse N))
        (compHomo
          (*Ty (Parse N))
          _
          N*Alg
          (initialAlgebra (*Ty (Parse N)))
          N*Homo
          (recHomo _ N*Alg))
        _
      )
      (ind-id'
        (TraceTy *NFA)
        (compHomo
          (TraceTy *NFA)
          _
          *NFAAlg
          (initialAlgebra (TraceTy *NFA))
          to*NFAHomo
          (recHomo _ *NFAAlg))
        (Sum.inl _)
      )
    where
    ⟦_⟧* : ⟨ *NFA .Q ⟩ → Grammar ℓN
    ⟦ Sum.inl _ ⟧* = Parse N *
    ⟦ Sum.inr q ⟧* = Trace N q ⊗ (Parse N *)

    ⟦_⟧N : ⟨ N .Q ⟩ → Grammar ℓN
    ⟦ q ⟧N = Trace *NFA (Sum.inl _) ⊸ Trace *NFA (Sum.inr q)

    *NFAAlg : Algebra (TraceTy *NFA) ⟦_⟧*
    *NFAAlg (Sum.inl _) = ⊕ᴰ-elim (λ {
        (stop Eq.refl) →
          NIL
          ∘g lowerG
          ∘g lowerG
      ; (stepε inr' Eq.refl) →
          CONS
          ∘g lowerG
      })
    *NFAAlg (Sum.inr q) = ⊕ᴰ-elim (λ {
        (step t Eq.refl) →
          STEP N t ,⊗ id
          ∘g ⊗-assoc
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG
      ; (stepε (cons⟨N⟩ acc) Eq.refl) →
          STOP N acc ,⊗ id
          ∘g ⊗-unit-l⁻
          ∘g lowerG
      ; (stepε (N-internal t) Eq.refl) →
          STEPε N t ,⊗ id
          ∘g lowerG
      })

    NAlg : Algebra (TraceTy N) ⟦_⟧N
    NAlg q = ⊕ᴰ-elim (λ {
        (stop acc) →
          ⊸-intro
            (STEPε *NFA (cons⟨N⟩ acc)
            ∘g ⊗-unit-l
            ∘g (lowerG ∘g lowerG) ,⊗ id)
      ; (step t Eq.refl) →
         ⊸-intro
           (STEP *NFA t
           ∘g id ,⊗ ⊸-app
           ∘g ⊗-assoc⁻
           ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
      ; (stepε t Eq.refl) →
         ⊸-intro
           (STEPε *NFA (N-internal t)
           ∘g ⊸-app
           ∘g lowerG ,⊗ id
           )
      })

    N*Alg : Algebra (*Ty (Parse N)) (λ _ → Parse *NFA)
    N*Alg _ = ⊕ᴰ-elim (λ {
        nil →
          STOP *NFA Eq.refl
          ∘g lowerG ∘g lowerG
      ; cons →
          STEPε *NFA inr'
          ∘g ⊸-app
          ∘g rec _ NAlg (N .init) ,⊗ id
          ∘g lowerG ,⊗ lowerG
      })

    to*NFA : ∀ q → ⟦ q ⟧* ⊢ Trace *NFA q
    to*NFA (Sum.inl _) = rec _ N*Alg _
    to*NFA (Sum.inr q) =
      ⊸-intro⁻ (rec _ NAlg q)
      ∘g id ,⊗ rec _ N*Alg _

    from*NFA : ∀ q → Trace *NFA q ⊢ ⟦ q ⟧*
    from*NFA = rec _ *NFAAlg

    -- This lemma is the key to the proof
    -- Like the previous iteration of this code with the old version of NFAs,
    -- I end up invoking the uniqueness principle of homomorphisms out of
    -- initial algebras
    -- I suspect this lemma could also be used for a proof involving equalizers,
    -- but this unqiue principle suffices
    nested-induction :
      ∀ q →
      rec _ *NFAAlg (Sum.inr q)
      ∘g ⊸-intro⁻ (rec _ NAlg q)
        ≡
      id ,⊗ rec _ *NFAAlg (Sum.inl _)
    nested-induction = nested-induction'
      where
      opaque
        unfolding ⊗-intro ⊗-unit-r⁻
        nested-induction' :
          ∀ q →
          rec _ *NFAAlg (Sum.inr q)
          ∘g ⊸-intro⁻ (rec _ NAlg q)
            ≡
          id ,⊗ rec _ *NFAAlg (Sum.inl _)
        nested-induction' q =
            equalizer-ind-⊗l
            (Tag N)
            _
            (λ q → Trace N q ⊗ (Parse N *))
            (λ _ → Trace *NFA (Sum.inl _))
            (λ q → rec _ *NFAAlg (Sum.inr q) ∘g ⊸-intro⁻ (rec _ NAlg q))
            (λ q → id ,⊗ rec _ *NFAAlg (Sum.inl _))
            (λ q → λ {
                (stop acc) →
                  rec _ *NFAAlg (Sum.inr q)
                  ∘g ⊸-intro⁻ (
                      ⊸-intro
                        (STEPε *NFA (cons⟨N⟩ acc)
                        ∘g ⊗-unit-l
                        ∘g (lowerG ∘g lowerG) ,⊗ id)
                     )
                  ∘g (liftG ∘g liftG) ,⊗ id
                  ∘g (lowerG ∘g lowerG) ,⊗ id
                    ≡⟨
                      (λ i →
                         rec _ *NFAAlg (Sum.inr q)
                         ∘g ⊸-β
                               (STEPε *NFA (cons⟨N⟩ acc)
                               ∘g ⊗-unit-l
                               ∘g (lowerG ∘g lowerG {ℓB = ℓN}) ,⊗ id) i
                         ∘g (liftG ∘g liftG {ℓB = ℓN}) ,⊗ id
                         ∘g (lowerG ∘g lowerG) ,⊗ id
                             )
                    ⟩
                  STOP N acc ,⊗ id
                  ∘g id ,⊗ rec _ *NFAAlg (Sum.inl _)
                  ∘g ⊗-unit-l⁻
                  ∘g ⊗-unit-l
                  ∘g (lowerG ∘g lowerG) ,⊗ id
                    ≡⟨
                      (λ i →
                         STOP N acc ,⊗ id
                         ∘g id ,⊗ rec _ *NFAAlg (Sum.inl _)
                         ∘g ⊗-unit-ll⁻ i
                         ∘g (lowerG ∘g lowerG) ,⊗ id
                      )
                    ⟩
                  id ,⊗ rec _ *NFAAlg (Sum.inl _)
                  ∘g STOP N acc ,⊗ id
                  ∘g (lowerG ∘g lowerG) ,⊗ id
                  ∎
              ; (step t Eq.refl) →
                  rec _ *NFAAlg (Sum.inr q)
                  ∘g ⊸-intro⁻ (
                     ⊸-intro
                       (STEP *NFA t
                       ∘g id ,⊗ ⊸-app
                       ∘g ⊗-assoc⁻
                       ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id)
                  )
                  ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
                  ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
                  ∘g (id ,⊗ eq-π _ _) ,⊗ id
                  ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                    ≡⟨
                      (λ i →
                         rec _ *NFAAlg (Sum.inr q)
                         ∘g ⊸-β (
                              STEP *NFA t
                              ∘g id ,⊗ ⊸-app
                              ∘g ⊗-assoc⁻
                              ∘g ((lowerG ∘g lowerG {ℓB = ℓN}) ,⊗ lowerG {ℓB = ℓN}) ,⊗ id) i
                         ∘g ((liftG ∘g liftG {ℓB = ℓN}) ,⊗ liftG) ,⊗ id
                         ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
                         ∘g (id ,⊗ eq-π _ _) ,⊗ id
                         ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                      )
                    ⟩
                  STEP N t ,⊗ id
                  ∘g ⊗-assoc
                  ∘g id ,⊗ rec _ *NFAAlg (Sum.inr (N .dst t))
                  ∘g id ,⊗ ⊸-app
                  ∘g id ,⊗ (rec _ NAlg (N .dst t) ,⊗ id)
                  ∘g id ,⊗ (eq-π _ _ ,⊗ id)
                  ∘g ⊗-assoc⁻
                  ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                    ≡⟨
                      (λ i →
                         STEP N t ,⊗ id
                         ∘g ⊗-assoc
                         ∘g id ,⊗ eq-π-pf-⊸-intro
                                    (rec _ *NFAAlg (Sum.inr (N .dst t))
                                    ∘g ⊸-intro⁻ (rec _ NAlg (N .dst t)))
                                    (id ,⊗ rec _ *NFAAlg (Sum.inl _))
                                    i
                         ∘g ⊗-assoc⁻
                         ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                      )
                    ⟩
                  STEP N t ,⊗ id
                  ∘g ⊗-assoc
                  ∘g ⊗-assoc⁻
                  ∘g id ,⊗ rec _ *NFAAlg (Sum.inl _)
                  ∘g (id ,⊗ eq-π _ _) ,⊗ id
                  ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                    ≡⟨
                      (λ i →
                         STEP N t ,⊗ id
                         ∘g ⊗-assoc∘⊗-assoc⁻≡id i
                         ∘g id ,⊗ rec _ *NFAAlg (Sum.inl _)
                         ∘g (id ,⊗ eq-π _ _) ,⊗ id
                         ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                      )
                    ⟩
                  id ,⊗ rec _ *NFAAlg (Sum.inl _)
                  ∘g STEP N t ,⊗ id
                  ∘g (id ,⊗ eq-π _ _) ,⊗ id
                  ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id
                  ∎
              ; (stepε t Eq.refl) →
                  rec _ *NFAAlg (Sum.inr q)
                  ∘g ⊸-intro⁻ (
                       ⊸-intro
                         (STEPε *NFA (N-internal t)
                         ∘g ⊸-app
                         ∘g lowerG ,⊗ id
                         )
                  )
                  ∘g liftG ,⊗ id
                  ∘g rec _ NAlg (N .ε-dst t) ,⊗ id
                  ∘g eq-π _ _ ,⊗ id
                  ∘g lowerG ,⊗ id
                    ≡⟨
                      (λ i →
                         rec _ *NFAAlg (Sum.inr q)
                         ∘g ⊸-β
                                (STEPε *NFA (N-internal t)
                                ∘g ⊸-app
                                ∘g lowerG {ℓB = ℓN} ,⊗ id
                                ) i
                         ∘g liftG ,⊗ id
                         ∘g rec _ NAlg (N .ε-dst t) ,⊗ id
                         ∘g eq-π _ _ ,⊗ id
                         ∘g lowerG ,⊗ id
                      )
                    ⟩
                  STEPε N t ,⊗ id
                  ∘g rec _ *NFAAlg (Sum.inr (N .ε-dst t))
                  ∘g ⊸-app
                  ∘g rec _ NAlg (N .ε-dst t) ,⊗ id
                  ∘g eq-π _ _ ,⊗ id
                  ∘g lowerG ,⊗ id
                    ≡⟨
                      (λ i →
                         STEPε N t ,⊗ id
                         ∘g eq-π-pf-⊸-intro _ _ i
                         ∘g lowerG ,⊗ id
                      )
                    ⟩
                  id ,⊗ rec _ *NFAAlg (Sum.inl _)
                  ∘g STEPε N t ,⊗ id
                  ∘g eq-π _ _ ,⊗ id
                  ∘g lowerG ,⊗ id
                  ∎
              })
            q

    N*Homo : Homomorphism (*Ty (Parse N)) N*Alg (initialAlgebra (*Ty (Parse N)))
    N*Homo .fst _ = from*NFA (Sum.inl _)
    N*Homo .snd _ = is-homo
      where
      opaque
        unfolding ⊗-intro ⊗-unit-r⁻
        is-homo :
          from*NFA (Sum.inl _) ∘g N*Alg _
          ≡
          roll ∘g map (*Ty (Parse N) _) λ _ → from*NFA (Sum.inl _)
        is-homo = ⊕ᴰ≡ _ _ λ {
            nil → refl
          ; cons →
            CONS
            ∘g from*NFA (Sum.inr (N .init))
            ∘g ⊸-intro⁻ (rec _ NAlg (N .init))
            ∘g lowerG ,⊗ lowerG
              ≡⟨
                (λ i →
                  CONS
                  ∘g nested-induction (N .init) i
                  ∘g lowerG ,⊗ lowerG
                )
              ⟩
            CONS
            ∘g id ,⊗ rec _ *NFAAlg (Sum.inl _)
            ∘g lowerG ,⊗ lowerG
            ∎
          }

    to*NFAHomo :
      Homomorphism
        (TraceTy *NFA)
        *NFAAlg
        (initialAlgebra (TraceTy *NFA))
    to*NFAHomo .fst = to*NFA
    to*NFAHomo .snd = is-homo
      where
      opaque
        unfolding ⊗-intro ⊗-unit-r⁻
        is-homo :
          ∀ q →
          to*NFA q ∘g *NFAAlg q
          ≡
          roll
          ∘g map (TraceTy *NFA q) (to*NFA)
        is-homo (Sum.inl _) =
          ⊕ᴰ≡ _ _
            λ {
            (stop Eq.refl) → refl
          ; (stepε inr' Eq.refl) → refl
           }
        is-homo (Sum.inr q) =
          ⊕ᴰ≡ _ _
            λ {
            (step t Eq.refl) →
              ⊸-app
              ∘g ⊸-intro
                   (STEP *NFA t
                   ∘g id ,⊗ ⊸-app
                   ∘g ⊗-assoc⁻
                   ∘g ((lowerG ∘g lowerG) ,⊗ lowerG) ,⊗ id) ,⊗ id
              ∘g ((liftG ∘g liftG) ,⊗ liftG) ,⊗ id
              ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
              ∘g id ,⊗ rec _ N*Alg _
              ∘g ⊗-assoc
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                ≡⟨
                  (λ i →
                     ⊸-β
                          (STEP *NFA t
                          ∘g id ,⊗ ⊸-app
                          ∘g ⊗-assoc⁻
                          ∘g ((lowerG ∘g lowerG {ℓB = ℓN}) ,⊗ lowerG {ℓB = ℓN}) ,⊗ id) i
                     ∘g ((liftG ∘g liftG {ℓB = ℓN}) ,⊗ liftG) ,⊗ id
                     ∘g (id ,⊗ rec _ NAlg (N .dst t)) ,⊗ id
                     ∘g id ,⊗ rec _ N*Alg _
                     ∘g ⊗-assoc
                     ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                  )
                ⟩
              STEP *NFA t
              ∘g id ,⊗ ⊸-app
              ∘g id ,⊗ (rec _ NAlg (N .dst t) ,⊗ id)
              ∘g id ,⊗ (id ,⊗ rec _ N*Alg _)
              ∘g ⊗-assoc⁻
              ∘g ⊗-assoc
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                ≡⟨
                  (λ i →
                     STEP *NFA t
                     ∘g id ,⊗ ⊸-app
                     ∘g id ,⊗ (rec _ NAlg (N .dst t) ,⊗ id)
                     ∘g id ,⊗ (id ,⊗ rec _ N*Alg _)
                     ∘g ⊗-assoc⁻∘⊗-assoc≡id i
                     ∘g (lowerG ∘g lowerG) ,⊗ lowerG
                  )
                ⟩
              STEP *NFA t
              ∘g id ,⊗ to*NFA (Sum.inr (N .dst t))
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
              ∎
          ; (stepε (cons⟨N⟩ acc) Eq.refl) →
             ⊸-intro⁻ (
               ⊸-intro
                 (STEPε *NFA (cons⟨N⟩ acc)
                 ∘g ⊗-unit-l
                 ∘g (lowerG ∘g lowerG) ,⊗ id)
             )
             ∘g (liftG ∘g liftG) ,⊗ id
             ∘g id ,⊗ rec _ N*Alg _
             ∘g ⊗-unit-l⁻
             ∘g lowerG
               ≡⟨
                 (λ i →
                    ⊸-β
                        (STEPε *NFA (cons⟨N⟩ acc)
                        ∘g ⊗-unit-l
                        ∘g (lowerG {ℓB = ℓN} ∘g lowerG {ℓB = ℓN}) ,⊗ id) i
                    ∘g (liftG ∘g liftG) ,⊗ id
                    ∘g id ,⊗ rec _ N*Alg _
                    ∘g ⊗-unit-l⁻
                    ∘g lowerG
                 )
               ⟩
             STEPε *NFA (cons⟨N⟩ acc)
             ∘g ⊗-unit-l
             ∘g ⊗-unit-l⁻
             ∘g rec _ N*Alg _
             ∘g lowerG
               ≡⟨
                 (λ i →
                   STEPε *NFA (cons⟨N⟩ acc)
                   ∘g ⊗-unit-l⁻l i
                   ∘g rec _ N*Alg _
                   ∘g lowerG
                 )
               ⟩
             STEPε *NFA (cons⟨N⟩ acc)
             ∘g to*NFA (Sum.inl _)
             ∘g lowerG
             ∎
          ; (stepε (N-internal t) Eq.refl) →
            ⊸-intro⁻ (
              ⊸-intro
                (STEPε *NFA (N-internal t)
                ∘g ⊸-app
                ∘g lowerG ,⊗ id
                )
            )
            ∘g liftG ,⊗ id
            ∘g rec _ NAlg (N .ε-dst t) ,⊗ id
            ∘g id ,⊗ rec _ N*Alg _
            ∘g lowerG
              ≡⟨
                (λ i →
                   ⊸-β
                       (STEPε *NFA (N-internal t)
                       ∘g ⊸-app
                       ∘g lowerG {ℓB = ℓN} ,⊗ id
                       ) i
                   ∘g liftG ,⊗ id
                   ∘g rec _ NAlg (N .ε-dst t) ,⊗ id
                   ∘g id ,⊗ rec _ N*Alg _
                   ∘g lowerG
                )
              ⟩
            STEPε *NFA (N-internal t)
            ∘g to*NFA (Sum.inr (N .ε-dst t))
            ∘g lowerG
            ∎
          }
