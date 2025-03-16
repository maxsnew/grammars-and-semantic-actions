open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.FinSet

module Turing.OneSided.Base
  (Alphabet : hSet ℓ-zero)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat
open import Cubical.Data.List hiding (init ; rec)
open import Cubical.Data.Bool
open import Cubical.Data.Maybe as Maybe
import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable ℓT : Level

-- For simplicity, assume that the input alphabet is {0,1}
-- and the tape alphabet adds a blank character
TapeAlphabet : hSet ℓ-zero
TapeAlphabet =
  ⟨ Alphabet ⟩ Sum.⊎ Unit , Sum.isSet⊎ (str Alphabet) isSetUnit

blank : ⟨ TapeAlphabet ⟩
blank = Sum.inr _

opaque
  isFinSetTapeAlphabet : isFinSet ⟨ TapeAlphabet ⟩
  isFinSetTapeAlphabet =
    isFinSet⊎ (_ , isFinSetAlphabet) (Unit , isFinSetUnit)

open import Grammar Alphabet
open import Grammar.Reify.Base Alphabet
import Grammar.Maybe.Base Alphabet as MaybeG
open import Term Alphabet

data Shift : Type where
  L R : Shift

record TuringMachine : Type (ℓ-suc ℓ-zero) where
  field
    Q : FinSet ℓ-zero
    init acc rej : ⟨ Q ⟩
    ¬acc≡rej : acc ≡ rej → Empty.⊥
    δ : ⟨ Q ⟩ → ⟨ TapeAlphabet ⟩ → ⟨ Q ⟩ × ⟨ TapeAlphabet ⟩ × Shift

  Tape : Type ℓ-zero
  Tape = ∀ (n : ℕ) → ⟨ TapeAlphabet ⟩

  Tape≡ : (t t' : Tape) → Type ℓ-zero
  Tape≡ t t' = ∀ n → t n ≡ t' n

  consTape : ⟨ TapeAlphabet ⟩ → Tape → Tape
  consTape c tape zero = c
  consTape c tape (suc n) = tape n

  Head : Type ℓ-zero
  Head = ℕ

  writeTape : Tape → Head → ⟨ TapeAlphabet ⟩ → Tape
  writeTape tape head c m =
    decRec
      (λ _ → c)
      (λ _ → tape m)
      (discreteℕ head m)

  blankTape : Tape
  blankTape n = blank

  initHead : Head
  initHead = 0

  initTape : String → Tape
  initTape [] = blankTape
  initTape (c ∷ w) = consTape (Sum.inl c) (initTape w)

  mkTransition : ⟨ Q ⟩ → Tape → Head → ⟨ Q ⟩ → ⟨ TapeAlphabet ⟩ → Shift → ⟨ Q ⟩ × Tape × Head
  mkTransition q tape zero nextState toWrite L = nextState , writeTape tape zero toWrite , zero
  mkTransition q tape (suc head) nextState toWrite L = nextState , writeTape tape (suc head) toWrite , head
  mkTransition q tape zero nextState toWrite R = nextState , writeTape tape zero toWrite , suc zero
  mkTransition q tape (suc head) nextState toWrite R = nextState , writeTape tape (suc head) toWrite , suc (suc head)

  transition : ⟨ Q ⟩ → Tape → Head → ⟨ Q ⟩ × Tape × Head
  transition q tape head =
    let nextState , toWrite , dir = δ q (tape head) in
    mkTransition q tape head nextState toWrite dir

module _ (TM : TuringMachine) where
  open TuringMachine TM

  -- Non-linearly transition within the Turing Machine
  data TuringTrace (b : Bool) : ⟨ Q ⟩ × Tape × Head → Type ℓ-zero where
    accept : ∀ t h → b ≡ true → TuringTrace b (acc , t , h)
    reject : ∀ t h → b ≡ false → TuringTrace b (rej , t , h)
    move : ∀ q t h →
      TuringTrace b (transition q t h) →
      TuringTrace b (q , t , h)

  AcceptingFrom : ⟨ Q ⟩ × Tape × Head → Type ℓ-zero
  AcceptingFrom (q , t , h) = TuringTrace true (q , t , h)

  RejectingFrom : ⟨ Q ⟩ × Tape × Head → Type ℓ-zero
  RejectingFrom (q , t , h) = TuringTrace false (q , t , h)

  Accepting : String → Type ℓ-zero
  Accepting w = AcceptingFrom (init , initTape (rev w) , initHead)

  Rejecting : String → Type ℓ-zero
  Rejecting w = RejectingFrom (init , initTape (rev w) , initHead)

  -- A grammar that accepts a string if it is accepted by
  -- a Turing machine
  Turing : Grammar ℓ-zero
  Turing = Reify Accepting

  decide-bounded : ∀ (fuel : ℕ) q t h → Maybe (AcceptingFrom (q , t , h))
  decide-bounded 0 q t h = nothing
  decide-bounded (suc n) q t h =
    decRec
      (λ acc≡q → just (subst (λ z → TuringTrace true (z , t , h)) acc≡q (accept t h refl)))
      (λ _ → nothing)
      (isFinSet→Discrete (str Q) acc q)

  decide-bounded' : ∀ (fuel : ℕ) → string ⊢ Reify λ w → Maybe (Accepting w)
  decide-bounded' n =
    readReify (λ w → Maybe (Accepting w))
    (λ w → decide-bounded n init (initTape (rev w)) initHead)

  -- Even though reification is powerful enough to describe
  -- unrestricted grammars, their membership is undecidable
  -- in general. The best algorithm that
  -- we may hope for is some bounded search procedure
  run : string ⊢ &[ fuel ∈ ℕ ] MaybeG.Maybe Turing
  run = &ᴰ-intro λ fuel →
    elimReify
      (λ w → Maybe (Accepting w))
      (λ w → Maybe.rec
        (MaybeG.nothing {A = ⌈ w ⌉} w (mk⌈⌉ w))
        λ accepts → MaybeG.just w (mkReify _ accepts)
      )
    ∘g decide-bounded' fuel
