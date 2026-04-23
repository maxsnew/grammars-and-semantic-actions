open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties using (Σ-Π-Iso)

module Automata.Deterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Parser Alphabet
open import Term Alphabet

private
  variable
    ℓ : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag : Type ℓ where
    stop step : Tag

  open Iso

  TagRep : Iso Tag Bool
  TagRep = iso
    (λ { stop → false ; step → true})
    (λ { false → stop ; true → step})
    (λ { false → refl ; true → refl})
    (λ { stop → refl ; step → refl})

  isSetTag : isSet Tag
  isSetTag = isSetRetract (TagRep .fun) (TagRep .inv) (TagRep .leftInv) isSetBool

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → (k (literal* c)) ⊗e (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

  STEP : ∀ c b q → ＂ c ＂ ⊗ Trace b (δ q c) ⊢ Trace b q
  STEP c b q = roll ∘g σ step ∘g σ (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG

  TraceF' : (q : Q) → Functor Q
  TraceF' q = ⊕e Tag λ {
      stop → ⊕e (Lift Bool) λ {(lift b) → (⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* })}
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → (k (literal* c)) ⊗e (Var (δ q c)) }) }

  open StrongEquivalence

  module _ {ℓ2 : Level} (X : Q → Grammar ℓ2) where
    parseNatTrans : (u : Unit*) → ⟦ *Ty char u ⟧ (λ _ → &[ q ∈ Q ] (X q)) ⊢ &[ q ∈ Q ] ⟦ TraceF' q ⟧ X
    parseNatTrans u = ⊕ᴰ-elim λ
      { nil → &ᴰ-intro nilCase
      ; cons → &ᴰ⊕ᴰ-dist≅ .inv ∘g σ (λ _ → step) ∘g (&ᴰ-intro consCase)
      } where
      nilCase : (q : Q) → ⟦ k {X = Unit*} ε* ⟧ (λ _ → &[ q ∈ Q ] (X q)) ⊢ ⟦ TraceF' q ⟧ X
      nilCase q = ε-elim (stop , ((lift (isAcc q)) , ((lift Eq.refl) , ((lift (lift ε-intro)))))) ∘g lowerG ∘g lowerG
      consCase : (q : Q) →
         (LiftG (ℓ-max ℓ2 ℓ) char ⊗ LiftG ℓ-zero (&[ q ∈ Q ] X q))
         ⊢ ⊕[ y ∈ Lift {i = ℓ-zero} {j = ℓ} ⟨ Alphabet ⟩ ]
         (LiftG {ℓA = ℓ} ℓ2 (literal* (y .lower)) ⊗ LiftG ℓ (X (δ q (y .lower))))
      consCase q =
        ⊕ᴰ-elim (λ c → σ (lift c) ∘g (liftG ∘g liftG) ,⊗ (liftG ∘g π (δ q c)))
        ∘g ⊕ᴰ-distL .fun
        ∘g lowerG ,⊗ lowerG

  baz : Algebra (*Ty char) λ _ → string
  baz = initialAlgebra (*Ty char)

  bez : Algebra TraceF' (μ TraceF')
  bez = initialAlgebra TraceF'

  biz : Algebra (*Ty char) (λ _ → &[ q ∈ Q ] ((μ TraceF') q))
  biz x = map&ᴰ bez ∘g parseNatTrans (μ TraceF') x

  fiz : Coalgebra TraceF' (λ _ → string)
  fiz x = π x ∘g parseNatTrans (λ _ → string) tt* ∘g map (*Ty char tt*) (λ _ → Δ) ∘g unroll (*Ty char) tt*

  parse1 : string ⊢ (&[ q ∈ Q ] (μ TraceF') q)
  parse1 = fold*r' char biz

  parse : string ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
  parse =
    fold*r char
      (&ᴰ-intro (λ q → σ (isAcc q) ∘g roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG))
      (&ᴰ-intro (λ q → ⊕ᴰ-elim (λ c → map⊕ᴰ (λ b → STEP c b q) ∘g ⊕ᴰ-distR .fun ∘g id ,⊗ π (δ q c)) ∘g ⊕ᴰ-distL .fun))

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
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      the-ret : π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
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
                  ∘g ⊕ᴰ-distR .fun
                  ∘g id ,⊗ eq-π-pf _ _ i
                  ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          )
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b

  isSetGrammarTrace : ∀ b q → isSetGrammar (Trace b q)
  isSetGrammarTrace b = isSetGrammarμ (TraceTy b) λ q →
    isSetTag , λ where
      stop → (isOfHLevelLift 2
               (isSetRetract Eq.eqToPath Eq.pathToEq
                Eq.pathToEq-eqToPath (isProp→isSet (isSetBool _ _)))) ,
             λ _ → isSetGrammarε*
      step → isOfHLevelLift 2 (Alphabet .snd) ,
             λ (lift y) → (isSetGrammarLift (isSetGrammarLiteral _)) , _

  open Parser

  AccTraceParser : ∀ q → Parser (Trace true q) (Trace false q)
  AccTraceParser q .disj =
    hasDisjointSummands⊕ᴰ isSetBool (unambiguous-⊕Trace q) true false true≢false
  AccTraceParser q .fun = Ind⊕→⊕ (λ b → Trace b q) ∘g π q ∘g parse
