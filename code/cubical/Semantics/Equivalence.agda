module Semantics.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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
    ℓg ℓh ℓk ℓl ℓ ℓ' ℓΣ₀ : Level
    Σ₀ : Type ℓΣ₀
    g : Grammar ℓg {Σ₀}
    h : Grammar ℓh {Σ₀}
    k : Grammar ℓk {Σ₀}
    l : Grammar ℓl {Σ₀}

-⊗η :
  ∀ {ℓg}{ℓh} →
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh {Σ₀}} →
  {k : Grammar ℓk {Σ₀}} →
  (e : g ⊢ h -⊗ k) →
  Term≡ {g = g} {h = h -⊗ k}
    e
    (λ-⊗[ x ∈ h ][ id {g = h} -⊗app[ h -⊗ k ] e ])
-⊗η {g = g}{h = h}{k = k} e {w} {p} =
  funExt (λ w' → funExt (λ ph →
    sym (transportRefl (e p w' (id {g = h} ph)))))

-⊗β :
  ∀ {ℓg}{ℓh} →
  {g : Grammar ℓg {Σ₀}} →
  {h : Grammar ℓh {Σ₀}} →
  {k : Grammar ℓk {Σ₀}} →
  {l : Grammar ℓl {Σ₀}} →
  (e : g ⊗ h ⊢ k) →
  (e' : l ⊢ g) →
  Term≡ {g = l ⊗ h} {h = k}
    (e' -⊗app[ g -⊗ k ] (λ-⊗[ x ∈ g ][ e ]))
    (trans {g = l ⊗ h} {h = g ⊗ h} {k = k}
      (cut {g = l} {h = g} (var ⊗l h) e')
      e)
-⊗β {g = g}{h = h}{k = k}{l = l} e e' {w} {p} = {!!}
