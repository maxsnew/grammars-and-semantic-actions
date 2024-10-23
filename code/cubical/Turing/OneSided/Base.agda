open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.FinSet

module Turing.OneSided.Base
  (Alphabet : hSet ℓ-zero)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Empty as Empty hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List hiding (init ; rec)
open import Cubical.Data.List.FinData
import Cubical.Data.Equality as Eq

private
  variable ℓT : Level

-- For simplicity, assume that the input alphabet is {0,1}
-- and the tape alphabet adds a blank character
TapeAlphabet : hSet ℓ-zero
TapeAlphabet =
  ⟨ Alphabet ⟩ ⊎ Unit , isSet⊎ (str Alphabet) isSetUnit

blank : ⟨ TapeAlphabet ⟩
blank = inr _

opaque
  isFinSetTapeAlphabet : isFinSet ⟨ TapeAlphabet ⟩
  isFinSetTapeAlphabet =
    isFinSet⊎ (_ , isFinSetAlphabet) (Unit , isFinSetUnit)

open import Grammar Alphabet
import Grammar.Maybe Alphabet as MaybeG
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Equivalence.Base Alphabet
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

  blankTape : Tape
  blankTape n = blank

  initHead : Head
  initHead = 0

  Accepting : ⟨ Q ⟩ × Tape × Head → Type ℓ-zero
  Accepting (q , t , h) = TuringTrace true (q , t , h)

  data Tag : Type ℓ-zero where
    nil snoc : Tag

  TuringTy : Tape → Functor Tape
  TuringTy tape =
    ⊕e Tag λ {
      nil → k ε
    ; snoc → ⊕e ⟨ Alphabet ⟩
      λ c → ⊕e (Σ[ tape' ∈ Tape ] Tape≡ (consTape (inl c) tape') tape) (λ (tape' , _) → ⊗e (Var tape') (k (literal c))) }

  -- The grammar of strings thats form the tape that have the input string in the leftmost
  -- entries of the tape
  TuringG : Tape → Grammar ℓ-zero
  TuringG tape = μ TuringTy tape

  open StrongEquivalence
  -- Linearly build the initial tape
  parseInitTape : string ⊢ ⊕[ tape ∈ Tape ] TuringG tape
  parseInitTape = fold*l char (λ _ → ⊕ᴰ-elim (λ {
        nil → ⊕ᴰ-in blankTape ∘g roll ∘g ⊕ᴰ-in nil ∘g lowerG
      ; snoc → (⊕ᴰ-elim (λ tape →
          ⊕ᴰ-elim (λ c → ⊕ᴰ-in (consTape (inl c) tape)
            ∘g roll ∘g ⊕ᴰ-in snoc ∘g ⊕ᴰ-in c ∘g ⊕ᴰ-in (tape , λ _ → refl) ∘g liftG ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun)
        ∘g ⊕ᴰ-distL .fun) ∘g lowerG ,⊗ lowerG}))

  -- From an input configuration, find an accepting trace, find a rejecting trace, or timeout
  decide-bounded :
    ∀ (fuel : ℕ) q t h → Maybe (Σ[ b ∈ Bool ] TuringTrace b (q , t , h))
  decide-bounded 0 q t h = nothing
  decide-bounded (suc n) q t h =
    decRec
      (λ acc≡q → just(true , subst (λ z → TuringTrace true (z , t , h)) acc≡q (accept t h refl)))
      (λ ¬acc≡q →
        decRec
          (λ rej≡q → just(false , subst (λ z → TuringTrace false (z , t , h)) rej≡q (reject t h refl)))
          (λ ¬rej≡q →
            let q' , t' , h' = transition q t h in
            let maybeTrace = decide-bounded n q' t' h' in
            map-Maybe (λ (b , trace) → b , move q t h trace) maybeTrace)
          (isFinSet→Discrete (str Q) rej q))
      (isFinSet→Discrete (str Q) acc q)

  run :
    (⊕[ tape ∈ Tape ] TuringG tape)
      ⊢
    &[ fuel ∈ ℕ ]
    MaybeG.Maybe (⊕[ tape ∈ Tape ]
                  ⊕[ b ∈ Bool ]
                  ⊕[ trace ∈ TuringTrace b (init , tape , initHead) ] TuringG tape)
  run = &ᴰ-intro λ fuel → ⊕ᴰ-elim (λ tape →
    let maybeTrace = decide-bounded fuel init tape initHead in
      Maybe.rec
        MaybeG.nothing
        (λ (b , trace) → MaybeG.return ∘g ⊕ᴰ-in tape ∘g ⊕ᴰ-in b ∘g ⊕ᴰ-in trace)
        maybeTrace)
