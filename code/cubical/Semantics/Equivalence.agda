module Semantics.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Semantics.Grammar
open import Semantics.String
open import Semantics.Helper
open import Semantics.Term

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    Σ₀ : Type ℓ-zero
    g : Grammar {Σ₀} ℓg
    h : Grammar {Σ₀} ℓh
    k : Grammar {Σ₀} ℓk
    l : Grammar {Σ₀} ℓl

-⊗η :
  ∀ {g : Grammar {Σ₀} ℓg} →
  (e : g ⊢ h -⊗ k) →
  Term≡ {g = g} {h = h -⊗ k}
    e
    (λ-⊗[ x ∈ h ][ id {g = h} -⊗app[ h -⊗ k ] e ])
-⊗η e {w} p =
  funExt (λ w' → funExt (λ ph → sym (transportRefl (e p w' ph))))

-⊗β :
  ∀ {g : Grammar {Σ₀} ℓg} →
  {h : Grammar {Σ₀} ℓh} →
  {k : Grammar {Σ₀} ℓk} →
  (e : g ⊗ h ⊢ k) →
  (e' : l ⊢ g) →
  Term≡ {g = l ⊗ h} {h = k}
    (e' -⊗app[ g -⊗ k ] (λ-⊗[ x ∈ g ][ e ]))
    (trans {g = l ⊗ h} {h = g ⊗ h} {k = k}
      (cut {g = l} {h = g} (var ⊗l h) e')
      e)
-⊗β {g = g}{h = h}{k = k} e e' p =
  {!!} ∙
  transportRefl (e (p .fst , e' (p .snd .fst) , p .snd .snd))
-- Goal: transp (λ i → k (p .fst .snd (~ i))) i0
--       (e
--        (((fst p .fst .fst , fst p .fst .snd) ,
--          (λ _ → fst p .fst .fst ++ fst p .fst .snd))
--         , e' (p .snd .fst) , p .snd .snd))
--       ≡
--       transp (λ i → k w) i0 (e (p .fst , e' (p .snd .fst) , p .snd .snd))
