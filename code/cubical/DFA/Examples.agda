open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Examples where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)
open import Cubical.Data.List hiding (init)

Alph = Fin 2
opaque
  isSetAlph : isSet Alph
  isSetAlph = isFinSet→isSet isFinSetFin

Alphabet : hSet ℓ-zero
Alphabet = (Alph , isSetAlph)

open import Grammar Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import Helper

open import String.Unicode
open import Cubical.Data.Maybe

unicode→Alphabet : UnicodeChar → Maybe ⟨ Alphabet ⟩
unicode→Alphabet c =
  decRec
    (λ _ → just fzero)
    (λ _ → decRec
            (λ _ → just (fsuc fzero))
            (λ _ → nothing)
            (DiscreteUnicodeChar '1' c))
    (DiscreteUnicodeChar '0' c)

open DecodeUnicode Alphabet unicode→Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

module examples where
  -- examples are over alphabet drawn from Fin 2
  -- characters are fzero and (fsuc fzero)
  D : DFAOver (Fin 3 , isFinSetFin)
  D .DeterministicAutomaton.init = fzero
  D .DeterministicAutomaton.isAcc fzero = true
  D .DeterministicAutomaton.isAcc (fsuc x) = false
  D .DeterministicAutomaton.δ fzero fzero = fromℕ 0
  D .DeterministicAutomaton.δ fzero (fsuc fzero) = fromℕ 1
  D .DeterministicAutomaton.δ (fsuc fzero) fzero = fromℕ 2
  D .DeterministicAutomaton.δ (fsuc fzero) (fsuc fzero) = fromℕ 0
  D .DeterministicAutomaton.δ (fsuc (fsuc fzero)) fzero = fromℕ 1
  D .DeterministicAutomaton.δ (fsuc (fsuc fzero)) (fsuc fzero) = fromℕ 2

  private
    module D = DeterministicAutomaton D

  opaque
    unfolding _⊕_ ⊕-elim ⊕-inl ⊕-inr ⟜-intro ⊸-intro _⊗_ ⌈w⌉→string ⊕ᴰ-distR ⊕ᴰ-distL
    mktest : String → Bool
    mktest w = (&ᴰ-π (D.init) ∘g D.parse) w (⌈w⌉→string {w = w} w (internalize w)) .fst

    _ : mktest (mkString "011") ≡ true
    _ = refl

    _ : mktest (mkString "0111") ≡ false
    _ = refl

    _ : mktest [] ≡ true
    _ = refl
