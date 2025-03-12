module Turing.OneSided.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
import Cubical.Data.SumFin as SumFin
import Cubical.Data.Sum as Sum
open import Cubical.Data.List
open import String.Unicode
import Agda.Builtin.Char as BuiltinChar
import Agda.Builtin.String as BuiltinString


Alphabet : hSet ℓ-zero
Alphabet = SumFin.Fin 2 , SumFin.isSetFin

isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩
isFinSetAlphabet = isFinSetFin

open import Grammar Alphabet
open import Turing.OneSided.Base Alphabet isFinSetAlphabet
module _ (TM : TuringMachine) where
  open TuringMachine TM
  z : ⟨ TapeAlphabet ⟩
  z = Sum.inl (Sum.inl tt)

  s : ⟨ TapeAlphabet ⟩
  s = Sum.inl (Sum.inr (Sum.inl tt))

  unicode→TapeAlphabet : UnicodeChar → Maybe ⟨ TapeAlphabet ⟩
  unicode→TapeAlphabet c =
    decRec
      (λ _ → just (Sum.inl (Sum.inl _)))
      (λ _ → decRec
              (λ _ → just (Sum.inl (Sum.inr (Sum.inl tt))))
              (λ _ → decRec
                       (λ _ → just (Sum.inr _))
                       (λ _ → nothing)
                       (DiscreteUnicodeChar ' ' c))
              (DiscreteUnicodeChar '1' c))
      (DiscreteUnicodeChar '0' c)

  mkTapeString : UnicodeString → List ⟨ TapeAlphabet ⟩
  mkTapeString w = filterMap unicode→TapeAlphabet (BuiltinString.primStringToList w)

  mkInputString : UnicodeString → String
  mkInputString w =
    filterMap
      (λ { (Sum.inl SumFin.fzero) → just (Sum.inl _)
         ; (Sum.inl (SumFin.fsuc SumFin.fzero)) → just (Sum.inr (Sum.inl tt))
         ; (Sum.inr tt) → nothing })
    (mkTapeString w)

  mkString : (w : UnicodeString) → string (mkInputString w)
  mkString w = ⌈w⌉→string {w = mkInputString w} (mkInputString w) (internalize (mkInputString w))

  w : UnicodeString
  w = "10101"

  t : Tape
  t = parseInitTape TM (mkInputString w) (mkString w) .fst
  opaque
    unfolding ⊸-intro ⊗-unit-l⁻ ⌈w⌉→string ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL
    -- these values are what we expect
    _ : (t 0 , t 1 , t 2 , t 3 , t 4 , t 5 , t 6 , t 12312312) ≡ (s , z , s , z , s , blank , blank , blank)
    _ = refl
