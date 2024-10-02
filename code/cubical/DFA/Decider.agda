open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Decider (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.List hiding (init)
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet as Idx
open import Grammar.Equivalence Alphabet
open import Grammar.String.Properties Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module _ (D : DFA) where
  open DFA D

  open *r-Algebra

  -- check-accept : {q-start : ⟨ Q ⟩} (q-end : ⟨ Q ⟩) →
  --   Trace q-end q-start ⊢
  --     AcceptingTrace q-start q-end ⊕ RejectingTrace q-start q-end
  -- check-accept q =
  --   decRec
  --     (λ acc → ⊕-inl ∘g LinΣ-intro acc)
  --     (λ rej → ⊕-inr ∘g LinΣ-intro rej)
  --     (isAcc q .snd)

  -- check-accept-from : (q-start : ⟨ Q ⟩) →
  --   TraceFrom q-start ⊢
  --     AcceptingTraceFrom q-start ⊕ RejectingTraceFrom q-start
  -- check-accept-from q-start =
  --   LinΣ-elim (λ q-end →
  --     ⊕-elim (⊕-inl ∘g LinΣ-intro q-end) (⊕-inr ∘g LinΣ-intro q-end) ∘g
  --     check-accept q-end)

  -- decide :
  --   string ⊢
  --     LinΠ[ q ∈ ⟨ Q ⟩ ] (AcceptingTraceFrom q ⊕ RejectingTraceFrom q)
  -- decide =
  --   LinΠ-intro (λ q →
  --     check-accept-from q ∘g
  --     LinΠ-app q) ∘g
  --   run-from-state

  -- decideInit :
  --   string ⊢
  --     (AcceptingTraceFrom init ⊕ RejectingTraceFrom init)
  -- decideInit = LinΠ-app init ∘g decide

  open StrongEquivalence

  parse-from-state : string ⊢ &[ q ∈ ⟨ Q ⟩ ] Trace' q
  parse-from-state = foldKL*r char the-alg
    where
    the-alg : *r-Algebra char
    the-alg .the-ℓ = ℓ-zero
    the-alg .G = &[ q ∈ ⟨ Q ⟩ ] Trace' q
    the-alg .nil-case =
      LinΠ-intro (λ q →
       roll ∘g LinΣ-intro stop)
    the-alg .cons-case =
      LinΠ-intro (λ q →
        LinΣ-elim (λ c →
          (roll ∘g LinΣ-intro step ∘g LinΣ-intro c) ∘g
          id ,⊗ LinΠ-app (δ q c)) ∘g ⊕ᴰ-dist .fun)

  printAlg : Algebra TraceTy λ _ → string
  printAlg q = LinΣ-elim ((λ {
      stop → NIL
    ; step → CONS ∘g LinΣ-elim (λ c → LinΣ-intro c ,⊗ id)
    }))

  print : (q : ⟨ Q ⟩) → Trace' q ⊢ string
  print q = Idx.rec TraceTy printAlg q

  Trace'≅string : (q : ⟨ Q ⟩) → StrongEquivalence (Trace' q) string
  Trace'≅string q .fun = print q
  Trace'≅string q .inv = LinΠ-app q ∘g parse-from-state
  Trace'≅string q .sec = unambiguous-string _ _
  Trace'≅string q .ret = ans
    where
    opaque
      unfolding NIL CONS KL*r-elim ⊕ᴰ-dist
      ans : LinΠ-app q ∘g parse-from-state ∘g print q ≡ id
      ans =
        ind-id' TraceTy
          (compHomo TraceTy (initialAlgebra _) printAlg (initialAlgebra _)
            ((λ q → LinΠ-app q ∘g parse-from-state) ,
            (λ q →
              ⊕ᴰ≡ _ _
                λ { stop → refl
                  ; step → refl
                  }
              ))
            (recHomo TraceTy printAlg))
          q
