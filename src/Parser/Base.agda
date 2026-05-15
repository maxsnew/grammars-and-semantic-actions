open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Parser.Base (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool using (Bool ; true ; false)

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

record Parser (A : Grammar ℓA) (B : Grammar ℓB) : Type (ℓ-max ℓA ℓB) where
  field
    disj : disjoint A B
    fun : string ⊢ A ⊕ B

  retTy : Grammar _
  retTy = A ⊕ B

open Parser
open WeakEquivalence

-- Utilities to benchmark a Parser
-- We actually don't need the disjointness to run the test,
-- so this isn't actually about the whole Parser type, just the fun field
-- This should probably get moved elsewhere then
module RunIncompleteParser {A : Grammar ℓA} {B : Grammar ℓB} (P : string ⊢ A ⊕ B) where
  private
    is-inl? : ∀ {X : Type ℓX} {Y : Type ℓY} →
      X Sum.⊎ Y → Bool
    is-inl? (Sum.inl x) = true
    is-inl? (Sum.inr y) = false

  opaque
    unfolding unfoldGrammarDefs
    run : (w : String) → (A ⊕ B) w
    run w = P w (mkstring w)

    accept? : (w : String) → Bool
    accept? w = is-inl? (run w)

  parse? : (w : String) → Type _
  parse? w = Σ[ x ∈ (A ⊕ B) w ] run w ≡ x

module RunParser {ℓA} {ℓB} {A : Grammar ℓA} {B : Grammar ℓB} (P : Parser A B)
  = RunIncompleteParser (P .fun)

opaque
  unfolding RunIncompleteParser.run
  unfoldParserDefs : Unit
  unfoldParserDefs = tt

module _ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
  (P : Parser A B) (A≈C : A ≈ C) where
  ≈Parser : Parser C B
  ≈Parser .disj = disjoint≈ (P .disj) A≈C
  ≈Parser .fun = A≈C .fun ,⊕p id ∘g P .fun
