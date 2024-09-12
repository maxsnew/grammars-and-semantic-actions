open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Examples where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)
open import Cubical.Data.List hiding (init)

Alphabet : hSet ℓ-zero
Alphabet = (Fin 2) , (isFinSet→isSet isFinSetFin)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import DFA.Decider Alphabet
open import Helper

module examples where
  -- examples are over alphabet drawn from Fin 2
  -- characters are fzero and (fsuc fzero)

  open DFA

  D : DFA
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

  _ : decide D _ (⌈ w ⌉) .fst ≡ true
  _ = refl

  _ : decide D _ (⌈ w' ⌉) .fst ≡ true
  _ = refl

  _ : decide D _ ⌈ w'' ⌉ .fst ≡ false
  _ = refl

  _ : decide D _ ⌈ [] ⌉ .fst ≡ true
  _ = refl


 {--       0
 -- 0  --------> 1
 --    <--------
 --        0
 -- and self loops for 1. state 1 is acc
 --
 --}
  D' : DFA
  Q D' = (Fin 2) , isFinSetFin
  init D' = inl _
  isAcc D' x =
    ((x ≡ fsuc fzero) , isSetFin x (fsuc fzero)) ,
    discreteFin x (fsuc fzero)
  δ D' fzero fzero = fromℕ 1
  δ D' fzero (fsuc fzero) = fromℕ 0
  δ D' (fsuc fzero) fzero = fromℕ 0
  δ D' (fsuc fzero) (fsuc fzero) = fromℕ 1

  s : String
  s = fsuc fzero ∷ fzero ∷ []

  _ : decide D' _ ⌈ s ⌉ .fst ≡ true
  _ = refl
