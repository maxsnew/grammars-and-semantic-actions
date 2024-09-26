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

Alphabet : hSet ℓ-zero
Alphabet = (Fin 2) , (isFinSet→isSet isFinSetFin)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import DFA.Decider Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

module examples where
  -- examples are over alphabet drawn from Fin 2
  -- characters are fzero and (fsuc fzero)

  open DFA

  opaque
    unfolding _⊕_ ⊕-elim ⊕-inl ⊕-inr ⟜-intro ⊸-intro _⊗_ ⌈w⌉→string KL*r-elim run-from-state
    is-inl : ∀ w → (g : Grammar ℓg) (h : Grammar ℓh) → (g ⊕ h) w → Bool
    is-inl w g h p = Sum.rec (λ _ → true) (λ _ → false) p

    mktest : ∀ {ℓd} → String → DFA {ℓd} → Bool
    mktest w dfa =
      is-inl w
        (AcceptingTraceFrom dfa (dfa .init)) (RejectingTraceFrom dfa (dfa .init))
        ((decideInit dfa ∘g (⌈w⌉→string {w = w})) w (internalize w))

    D : DFA {ℓ-zero}
    D .Q = Fin 3 , isFinSetFin
    D .init = fzero
    D .isAcc fzero = (Unit , isPropUnit ) , yes _
    D .isAcc (fsuc x) = (Empty.⊥* , isProp⊥*) , no lower
    δ D fzero fzero = fromℕ 0
    δ D fzero (fsuc fzero) = fromℕ 1
    δ D (fsuc fzero) fzero = fromℕ 2
    δ D (fsuc fzero) (fsuc fzero) = fromℕ 0
    δ D (fsuc (fsuc fzero)) fzero = fromℕ 1
    δ D (fsuc (fsuc fzero)) (fsuc fzero) = fromℕ 2

    w : String
    w = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fzero ∷ []

    w' : String
    w' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

    w'' : String
    w'' = fzero ∷ fsuc fzero ∷ fsuc fzero ∷ fsuc fzero ∷ []

    _ : mktest w' D ≡ true
    _ = refl

   --  _ : mktest w'' D ≡ false
   --  _ = refl

   --  _ : mktest [] D ≡ true
   --  _ = refl


   -- {--       0
   -- -- 0  --------> 1
   -- --    <--------
   -- --        0
   -- -- and self loops for 1. state 1 is acc
   -- --
   -- --}
   --  D' : DFA {ℓ-zero}
   --  Q D' = (Fin 2) , isFinSetFin
   --  init D' = inl _
   --  isAcc D' x =
   --    ((x ≡ fsuc fzero) , isSetFin x (fsuc fzero)) ,
   --    discreteFin x (fsuc fzero)
   --  δ D' fzero fzero = fromℕ 1
   --  δ D' fzero (fsuc fzero) = fromℕ 0
   --  δ D' (fsuc fzero) fzero = fromℕ 0
   --  δ D' (fsuc fzero) (fsuc fzero) = fromℕ 1

   --  s : String
   --  s = fsuc fzero ∷ fzero ∷ []

   --  _ : mktest s D' ≡ true
   --  _ = refl
