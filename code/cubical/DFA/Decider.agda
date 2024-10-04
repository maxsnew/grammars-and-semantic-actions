open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Decider (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.List hiding (init)
import Cubical.Data.Equality as Eq


open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet as Idx
open import Grammar.Equivalence Alphabet
open import Grammar.String.Properties Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module _ (D : DFA) where
  open DFA D

  open *r-Algebra

  open StrongEquivalence

  parse : string ⊢ &[ q ∈ ⟨ Q ⟩ ] ⊕[ b ∈ Bool ] Trace b q
  parse = foldKL*r char the-alg
    where
    the-alg : *r-Algebra char
    the-alg .the-ℓ = ℓ-zero
    the-alg .G = &[ q ∈ ⟨ Q ⟩ ] ⊕[ b ∈ Bool ] Trace b q
    the-alg .nil-case =
      &ᴰ-in (λ q → ⊕ᴰ-in (isAcc q) ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in Eq.refl)
    the-alg .cons-case =
      &ᴰ-in λ q →
        ⊕ᴰ-elim (λ c →
          ⊕ᴰ-elim
            (λ b → ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c) ∘g
          ⊕ᴰ-distR .fun ∘g
          id ,⊗ &ᴰ-π (δ q c)) ∘g
        ⊕ᴰ-distL .fun

  printAlg : ∀ b → Algebra (TraceTy b) λ _ → string
  printAlg b q = ⊕ᴰ-elim ((λ {
      stop → ⊕ᴰ-elim λ { Eq.refl → NIL }
    ; step → CONS ∘g ⊕ᴰ-elim (λ c → ⊕ᴰ-in c ,⊗ id)
    }))

  print : ∀ b → (q : ⟨ Q ⟩) → Trace b q ⊢ string
  print b q = Idx.rec (TraceTy b) (printAlg b) q

  ⊕ᴰalg : ∀ b → Algebra (TraceTy b) λ q → ⊕[ b ∈ Bool ] Trace b q
  ⊕ᴰalg b q = ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim λ {
        Eq.refl → ⊕ᴰ-in (isAcc q) ∘g roll ∘g ⊕ᴰ-in stop ∘g ⊕ᴰ-in Eq.refl}
    ; step →
        ⊕ᴰ-elim (λ c → ⊕ᴰ-elim (λ b →
          ⊕ᴰ-in b ∘g roll ∘g ⊕ᴰ-in step ∘g ⊕ᴰ-in c)
          ∘g ⊕ᴰ-distR .fun)
    })

  Trace≅string :
    (q : ⟨ Q ⟩) → StrongEquivalence (⊕[ b ∈ Bool ] Trace b q) string
  Trace≅string q .fun = ⊕ᴰ-elim (λ b → print b q)
  Trace≅string q .inv = &ᴰ-π q ∘g parse
  Trace≅string q .sec =  unambiguous-string _ _
  Trace≅string q .ret =  ans
    where
    opaque
      unfolding NIL CONS KL*r-elim ⊕ᴰ-distR
      ans : &ᴰ-π q ∘g parse ∘g ⊕ᴰ-elim (λ b → print b q) ≡ id
      ans = ⊕ᴰ≡ _ _ λ b →
        ind'
          (TraceTy b)
          (⊕ᴰalg b)
          ((λ q'  → &ᴰ-π q' ∘g parse ∘g print b q') ,
          λ q' → ⊕ᴰ≡ _ _ (λ {
            stop → funExt λ w → funExt λ { (Eq.refl , p) → refl}
          ; step → ⊕ᴰ≡ _ _ λ c → refl }))
          ((λ q' → ⊕ᴰ-in b) ,
          λ q' → ⊕ᴰ≡ _ _ λ {
            stop → funExt (λ w → funExt λ { (Eq.refl , p) → refl})
          ; step → refl })
          q

  unambiguous-⊕Trace : ∀ q → unambiguous (⊕[ b ∈ Bool ] Trace b q)
  unambiguous-⊕Trace q =
   unambiguous≅ (sym-strong-equivalence (Trace≅string q)) unambiguous-string

  unambiguous-Trace : ∀ b q → unambiguous (Trace b q)
  unambiguous-Trace b q = unambiguous⊕ᴰ isSetBool (unambiguous-⊕Trace q) b
