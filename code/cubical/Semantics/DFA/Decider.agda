open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.DFA.Decider ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List hiding (init)

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
open import Semantics.DFA.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

String→KL* : (w : String) → KL* ⊕Σ₀ w
String→KL* [] = nil _ refl
String→KL* (x ∷ w) =
  cons _ ((([ x ] , w) , refl) , (((x , refl)) , (String→KL* w)))

module _ (D : DFA {ℓD}) where
  open DFA D

  open *l-Algebra
  open Algebra
  open AlgebraHom

  module _ (q-start : ⟨ Q ⟩) where
    TraceFrom : Grammar ℓD
    TraceFrom = LinΣ[ q-end ∈ ⟨ Q ⟩ ] Trace q-end q-start

    ExtendTraceFrom : (c : Σ₀) →
      TraceFrom ⊗ (literal c) ⊢ TraceFrom
    ExtendTraceFrom c _ (s , (q , trace), lit) =
      (δ q c) ,
      TraceAppendLiteral q-start q c _ (s , (trace , lit))

    RunFromState : KL* ⊕Σ₀ ⊢ TraceFrom
    RunFromState = foldKL*l ⊕Σ₀ the-alg
      where
      the-alg : *l-Algebra ⊕Σ₀
      the-alg .the-ℓ = ℓD
      the-alg .G = TraceFrom
      the-alg .nil-case w pε = q-start , (nil _ pε)
      the-alg .snoc-case w (s , trFrom , (c , lit)) =
        ExtendTraceFrom c w (s , (trFrom , lit))

    DecideFromState : String → Bool
    DecideFromState w =
      let (q-end , trace) = RunFromState _ (String→KL* w) in
      decRec
        (λ acc → true)
        (λ ¬acc → false)
        (isAcc q-end .snd)

  Decide : String → Bool
  Decide = DecideFromState init

