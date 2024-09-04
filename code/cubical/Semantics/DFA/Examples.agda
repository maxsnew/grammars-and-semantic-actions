open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.DFA.Examples where

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

Alphabet : hSet ℓ-zero
Alphabet = (Fin 2) , (isFinSet→isSet isFinSetFin)

Σ₀ = Alphabet .fst
isSetΣ₀ = Alphabet .snd

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
open import Semantics.DFA.Base (Σ₀ , isSetΣ₀)
open import Semantics.DFA.Decider (Σ₀ , isSetΣ₀)
open import Semantics.Helper

module examples where
  -- examples are over alphabet drawn from Fin 2
  -- characters are fzero and (fsuc fzero)

  open DFA

  D : DFA
  D .Q = Fin 3 , isFinSetFin
  D .init = fzero
  D .isAcc fzero = (Unit , isPropUnit ) , yes _
  D .isAcc (fsuc x) = (⊥* , isProp⊥*) , no lower
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

  ex1 : Decide D w ≡ true
  ex1 = refl

  ex2 : Decide D w' ≡ true
  ex2 = refl

  ex3 : Decide D w'' ≡ false
  ex3 = refl

  ex4 : Decide D [] ≡ true
  ex4 = refl


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

  ex5 : Decide D' s ≡ true
  ex5 = refl