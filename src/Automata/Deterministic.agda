{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automata.Deterministic (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
import Erased.Data.Equality as Eq
import Erased.Data.Empty as Empty
import Cubical.Data.Empty as CubicalEmpty
open import Erased.Lift.Base

open import Grammar Alphabet isSetAlphabet
open import Parser Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsIndexed Alphabet isSetAlphabet as Idx⊕
open import Term Alphabet isSetAlphabet

private
  variable
    ℓ : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → Alphabet → Q

  data Tag : Type ℓ where
    stop step : Tag

  open Iso

  @0 TagRep : Iso Tag Bool
  TagRep = iso
    (λ { stop → false ; step → true})
    (λ { false → stop ; true → step})
    (λ { false → refl ; true → refl})
    (λ { stop → refl ; step → refl})

  @0 isSetTag : isSet Tag
  isSetTag = isSetRetract (TagRep .fun) (TagRep .inv) (TagRep .leftInv) isSetBool

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift Alphabet) (λ { (lift c) → (k (literal* c)) ⊗e (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

  STEP : ∀ c b q → ＂ c ＂ ⊗ Trace b (δ q c) ⊢ Trace b q
  STEP c b q = roll ∘g σ step ∘g σ (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG

  open StrongEquivalence

  parse : string ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
  parse =
    fold*r char
      (&ᴰ-intro (λ q → σ (isAcc q) ∘g roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG))
      (&ᴰ-intro (λ q → ⊕ᴰ-elim (λ c → map⊕ᴰ (λ b → STEP c b q) ∘g ⊕ᴰ-distREq .fun ∘g id ,⊗ π (δ q c)) ∘g ⊕ᴰ-distLEq .fun))

  parseInit : string ⊢ ⊕[ b ∈ Bool ] Trace b init
  parseInit = π init ∘g parse

  printAlg : ∀ b → Algebra (TraceTy b) (λ _ → string)
  printAlg b q = ⊕ᴰ-elim λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → NIL ∘g lowerG ∘g lowerG })
    ; step → CONS ∘g ⊕ᴰ-elim (λ { (lift c) → σ c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG }) }

  print : ∀ b → (q : Q) → Trace b q ⊢ string
  print b q = rec (TraceTy b) (printAlg b) q

  Trace≅string : (q : Q) → ⊕[ b ∈ Bool ] Trace b q ≅ string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = π q ∘g parse
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distREq ⊕ᴰ-distLEq ⊗-intro
      @0 the-ret : π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      the-ret =
        ⊕ᴰ≡ _ _ λ b →
        equalizer-ind (TraceTy b)
          (λ q → ⊕[ b ∈ Bool ] Trace b q)
          (λ q → π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ∘g σ b)
          (λ q → σ b)
          (λ q →
            ⊕ᴰ≡ _ _ λ where
              stop → ⊕ᴰ≡ _ _ λ where
                (lift Eq.refl) → refl
              step → ⊕ᴰ≡ _ _ λ where
                (lift c) i →
                  map⊕ᴰ (λ b' → STEP c b' q)
                  ∘g ⊕ᴰ-distREq .fun
                  ∘g id ,⊗ eq-π-pf _ _ i
                  ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          )
          q

  @0 unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  @0 unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = Idx⊕.unambig-summands (unambiguous-⊕Trace q) b

  -- @0 isSetGrammarTrace : ∀ b q → isSetGrammar (Trace b q)
  -- isSetGrammarTrace b = {!!}
    -- isSetGrammarμ (TraceTy b) λ q →
    -- isSetTag , λ where
    --   stop → (isOfHLevelLift 2
    --            (isSetRetract Eq.eqToPath Eq.pathToEq
    --             Eq.pathToEq-eqToPath (isProp→isSet (isSetBool _ _)))) ,
    --          λ _ → isSetGrammarε*
    --   step → isOfHLevelLift 2 (Alphabet .snd) ,
    --          λ (lift y) → (isSetGrammarLift (isSetGrammarLiteral _)) , _

  open Parser

  AccTraceParser : ∀ q → Parser (Trace true q) (Trace false q)
  AccTraceParser q .disj =
    hasDisjointSummands⊕ᴰ (unambiguous-⊕Trace q) true false λ t≡f → CubicalEmpty.rec (true≢false t≡f)
  AccTraceParser q .fun = Ind⊕→⊕ (λ b → Trace b q) ∘g π q ∘g parse
