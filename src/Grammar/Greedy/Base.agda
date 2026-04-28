open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Greedy.Base (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓA : Level

module _ (A : Grammar ℓA) where
  -- A leftmost greedy parse of A is a parse of A over some string w
  -- and a proof that no larger string with w as a proper prefix could have
  -- had an A parse over it
  Greedy : Grammar ℓA
  Greedy = ⊕[ w ∈ String ] ((⌈ w ⌉ & A) ⊗ ¬G (((A ⟜ ⌈ w ⌉) & char +) ⊗ ⊤))

  Greedy→leftmost : Greedy ⊢ A ⊗ ⊤
  Greedy→leftmost = ⊕ᴰ-elim (λ w → π₂ ,⊗ ⊤-intro)

  GreedyCompl : Grammar ℓA
  GreedyCompl = ¬G (A ⊗ ⊤)

  disjointGreedy-GreedyCompl : disjoint Greedy GreedyCompl
  disjointGreedy-GreedyCompl = ⇒-app ∘g &-swap ∘g Greedy→leftmost ,&p id
