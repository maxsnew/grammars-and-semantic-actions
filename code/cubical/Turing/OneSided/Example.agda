module Turing.OneSided.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Maybe
open import Cubical.Data.SumFin
open import Cubical.Data.List
open import String.Unicode
import Agda.Builtin.Char as BuiltinChar
import Agda.Builtin.String as BuiltinString


Alphabet : hSet ℓ-zero
Alphabet = Fin 2 , isSetFin

isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩
isFinSetAlphabet = isFinSetFin

open import Grammar Alphabet
open import Turing.OneSided.Base Alphabet isFinSetAlphabet
module _ (TM : TuringMachine) where
  open TuringMachine TM
  z : ⟨ TapeAlphabet ⟩
  z = inl (inl tt)

  s : ⟨ TapeAlphabet ⟩
  s = inl (inr (inl tt))

  unicode→TapeAlphabet : UnicodeChar → Maybe ⟨ TapeAlphabet ⟩
  unicode→TapeAlphabet c =
    decRec
      (λ _ → just (inl (inl _)))
      (λ _ → decRec
              (λ _ → just (inl (inr (inl tt))))
              (λ _ → decRec
                       (λ _ → just (inr _))
                       (λ _ → nothing)
                       (DiscreteUnicodeChar ' ' c))
              (DiscreteUnicodeChar '1' c))
      (DiscreteUnicodeChar '0' c)

  mkTapeString : UnicodeString → List ⟨ TapeAlphabet ⟩
  mkTapeString w = filterMap unicode→TapeAlphabet (BuiltinString.primStringToList w)

  mkInputString : UnicodeString → String
  mkInputString w =
    filterMap
      (λ { (inl fzero) → just (inl _)
         ; (inl (fsuc fzero)) → just (inr (inl tt))
         ; (fsuc tt) → nothing })
    (mkTapeString w)

  mkString : (w : UnicodeString) → string (mkInputString w)
  mkString w = ⌈w⌉→string {w = mkInputString w} (mkInputString w) (internalize (mkInputString w))

  w : UnicodeString
  w = "10101"

  t : Tape
  t = parseInitTape TM (mkInputString w) (mkString w) .fst
  opaque
    unfolding ⟜-intro ⊗-unit-l⁻ ⌈w⌉→string ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL
    -- these values are what we expect
    _ : (t 0 , t 1 , t 2 , t 3 , t 4 , t 5 , t 6 , t 12312312) ≡ (s , z , s , z , s , blank , blank , blank)
    _ = refl
