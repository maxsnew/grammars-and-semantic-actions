open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Automaton.Deterministic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Equivalence.Base Alphabet
import Cubical.Data.Equality as Eq
open import Term Alphabet
open import Helper

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

  TraceTy : Bool → (q : Q) → Functor Q
  TraceTy b q = ⊕e Tag λ {
      stop → ⊕e (Lift (b Eq.≡ isAcc q)) λ { (lift acc) → k ε* }
      ; step → ⊕e (Lift ⟨ Alphabet ⟩) (λ { (lift c) → ⊗e (k (literal* c)) (Var (δ q c)) }) }

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b = μ (TraceTy b)

  open StrongEquivalence
  parseAlg : Algebra (*Ty char) λ _ → &[ q ∈ Q ] ⊕[ b ∈ Bool ] Trace b q
  parseAlg _ = ⊕ᴰ-elim (λ {
    nil → &ᴰ-in (λ q →
      ⊕ᴰ-in (isAcc q) ∘g
      roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) ∘g
      liftG ∘g liftG ∘g lowerG ∘g lowerG)
    ; cons → &ᴰ-in (λ q → (
      ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun
          ∘g id ,⊗ &ᴰ-π (δ q c))
      ∘g ⊕ᴰ-distL .fun)
      ∘g lowerG ,⊗ lowerG) })

  parse : string ⊢ &[ q ∈ Q ] ⊕[ b ∈ Bool ] Trace b q
  parse = rec (*Ty char) parseAlg _

  printAlg : ∀ b → Algebra (TraceTy b) (λ _ → string)
  printAlg b q = ⊕ᴰ-elim λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → NIL ∘g lowerG ∘g lowerG })
    ; step → CONS ∘g ⊕ᴰ-elim (λ { (lift c) → ⊕ᴰ-in c ,⊗ id ∘g (lowerG ∘g lowerG) ,⊗ lowerG }) }

  print : ∀ b → (q : Q) → Trace b q ⊢ string
  print b q = rec (TraceTy b) (printAlg b) q

  ⊕ᴰAlg : ∀ b → Algebra (TraceTy b) (λ q → ⊕[ b ∈ Bool ] Trace b q)
  ⊕ᴰAlg b q = ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift Eq.refl) → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in (lift Eq.refl) })
    ; step → ⊕ᴰ-elim (λ c →
        ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c ∘g (liftG ∘g liftG) ,⊗ liftG)
          ∘g ⊕ᴰ-distR .fun ∘g (lowerG ∘g lowerG) ,⊗ lowerG) })

  Trace≅string : (q : Q) → StrongEquivalence (⊕[ b ∈ Bool ] Trace b q) string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = &ᴰ-π q ∘g parse
  Trace≅string q .sec = unambiguous-string _ _
  Trace≅string q .ret = isRetract
    where
    opaque
      unfolding ⊕ᴰ-distR ⊕ᴰ-distL ⊗-intro
      isRetract : &ᴰ-π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      isRetract = ⊕ᴰ≡ _ _ λ b →
        ind'
          (TraceTy b)
          (⊕ᴰAlg b)
          ((λ q'  → &ᴰ-π q' ∘g parse ∘g print b q') ,
          λ q' → ⊕ᴰ≡ _ _ (λ {
            stop → funExt λ w → funExt λ {
              ((lift Eq.refl) , p) → refl}
          ; step → ⊕ᴰ≡ _ _ (λ { (lift c) → refl })
          }))
          ((λ q' → ⊕ᴰ-in b) ,
          λ q' → ⊕ᴰ≡ _ _ λ {
            stop → funExt (λ w → funExt λ {
              ((lift Eq.refl) , p) → refl})
          ; step → refl })
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b
