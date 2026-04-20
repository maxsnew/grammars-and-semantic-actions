open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties using (Σ-Π-Iso)

module Automata.Deterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

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

  data Tag' : Type ℓ where
    stop√ stop× step : Tag'

  TraceF' : (q : Q) → Functor Q
  TraceF' q = ⊕e Tag' λ {
      stop√ → ⊕e (Lift (true Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; stop× → ⊕e (Lift (false Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → (k (literal* c)) ⊗e (Var (δ q c)) }) }

  open StrongEquivalence

  module _ (X : Grammar ℓ) where
    private --else in where clause
      foo : (LiftG ℓ (λ w → Σ ⟨ Alphabet ⟩ (λ x → literal x w)) ⊗ LiftG ℓ-zero X) ⊢ ⊕ᴰ (λ y → LiftG ℓ (literal* (y .lower)) ⊗ LiftG ℓ X)
      foo = ⊕ᴰ-distL .fun ∘g ⊗-intro (λ w z → lift (z .lower .fst) , lift (lift (z .lower .snd))) (liftG ∘g lowerG)
    parseNatTrans : (q : Q) → ⟦ *Ty char _ ⟧ (λ _ → X) ⊢ ⟦ TraceF' q ⟧ (λ _ → X)
    parseNatTrans q with (isAcc q) in eq
    ... | true = ⊕ᴰ-elim λ
      { nil →
        (λ w x → stop√ , ((lift (Eq.sym eq)) , lift (lift (lower (lower x)))))
      ; cons → (λ z → Σ-Π-Iso .inv ((λ _ → step) , foo z))
      }
    ... | false = ⊕ᴰ-elim λ
      { nil → (λ w x → stop× , ((lift (Eq.sym eq)) , lift (lift (lower (lower x)))))
      ; cons → (λ z → Σ-Π-Iso .inv ((λ _ → step) , foo z)) }

  module _ {ℓ2 : Level} (X : Grammar ℓ2) where
    parseNatTrans2 : ⟦ *Ty char _ ⟧ (λ _ → X) ⊢ &[ q ∈ Q ] ⟦ TraceF' q ⟧ (λ _ → X)
    parseNatTrans2 =
     ⊕ᴰ-elim λ
      { nil → λ w llεw q →  foo llεw q
      ; cons → &ᴰ-intro λ q w → Σ-Π-Iso .inv ((λ _ → step) , baz w) -- (λ z → Σ-Π-Iso .inv ((λ _ → step) , foo z))
      } where
      foo : {w : String} → (Lift (Lift (ε w))) → (q : Q) → ⟦ TraceF' q ⟧ (λ _ → X) w
      foo llεw q with (isAcc q) in eq
      ... | false = stop× , ((lift (Eq.sym eq)) , lift (lift (lower (lower llεw))))
      ... | true  = stop√ , ((lift (Eq.sym eq)) , lift (lift (lower (lower llεw))))
      baz : (LiftG ℓ2 char ⊗ LiftG ℓ-zero X) ⊢ ⊕ᴰ (λ y → LiftG ℓ2 (literal* (y .lower)) ⊗ LiftG ℓ X)
      baz = ⊕ᴰ-distL .fun ∘g ⊗-intro (λ w z → lift (z .lower .fst) , lift (lift (z .lower .snd))) (liftG ∘g lowerG)


  baz : Algebra (*Ty char) λ _ → KL* char
  baz = initialAlgebra (*Ty char)

  biz : Algebra (*Ty char) (λ _ → &[ q ∈ Q ] ⟦ TraceF' q ⟧ (μ TraceF')) -- (λ q → (⟦ TraceF' q ⟧ (λ _ → (μ TraceF'))))
  biz = {!parseNatTrans (KL* char)!}

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
