open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.LinearProduct ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓG' : Level

_⊗_ : Grammar ℓG → Grammar ℓG' → Grammar (ℓ-max ℓG ℓG')
(g ⊗ g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)
infixr 20 _⊗_

⊗PathP : {g : I → Grammar ℓG}{g' : I → Grammar ℓG'}
  {w : I → String}
  → {p : (g i0 ⊗ g' i0) (w i0)}
  → {q : (g i1 ⊗ g' i1) (w i1)}
  → (s≡ : p .fst .fst ≡ q .fst .fst)
  → PathP (λ i → g i (s≡ i .fst) × g' i (s≡ i .snd)) (p .snd) (q .snd)
  → PathP (λ i → (g i ⊗ g' i) (w i)) p q
⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

⊗≡ : ∀ {g : Grammar ℓG}{g' : Grammar ℓG'}{w}
  → (p p' : (g ⊗ g') w)
  → (s≡ : p .fst .fst ≡ p' .fst .fst)
  → PathP (λ i → g (s≡ i .fst) × g' (s≡ i .snd)) (p .snd) (p' .snd)
  → p ≡ p'
⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡
