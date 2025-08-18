{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp.Alphabet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

data Tok : Type where
  [ ] : Tok     -- parens
  + : Tok       -- the binary operation
  num : ℕ → Tok -- constants

LP = [
RP = ]
PLUS = +

open Iso
opaque
  TokRep : Iso Tok (Bool ⊎ (Unit ⊎ ℕ))
  TokRep =
      iso
        (λ { [ → Sum.inl true ; ] → Sum.inl false
           ; + → Sum.inr (Sum.inl _) ; (num x) → Sum.inr (Sum.inr x)})
        (λ { (Sum.inl false) → ] ; (Sum.inl true) → [ ; (Sum.inr (Sum.inl x)) → +
           ; (Sum.inr (Sum.inr x)) → num x})
        (λ { (Sum.inl false) → refl ; (Sum.inl true) → refl ; (Sum.inr (Sum.inl x)) → refl
           ; (Sum.inr (Sum.inr x)) → refl})
        λ { [ → refl ; ] → refl ; + → refl ; (num x) → refl}

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .leftInv)
      (Sum.isSet⊎ isSetBool (Sum.isSet⊎ isSetUnit isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

+≢[ : Tok.+ Eq.≡ Tok.[ → Empty.⊥
+≢[ ()

+≢] : Tok.+ Eq.≡ Tok.] → Empty.⊥
+≢] ()

+≢num : ∀ x → Tok.+ Eq.≡ Tok.num x → Empty.⊥
+≢num x ()

open import Grammar Alphabet hiding (_+)
open import Parser Alphabet
open import Term Alphabet

open StrongEquivalence

anyNum : Grammar _
anyNum = ⊕[ n ∈ ℕ ] ＂ num n ＂

mkAnyNum : ∀ {n} → literal (num n) ⊢ anyNum
mkAnyNum = σ _
