open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Automata.Deterministic.FusableParse (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Parser Alphabet
open import Term Alphabet
open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Literal Alphabet
open import Grammar.String.Liftless Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Inductive.Liftless.Indexed Alphabet
open import Grammar.Inductive.Liftless.Structure Alphabet

private
  variable
    ℓ ℓ' : Level

record DeterministicAutomaton (Q : Type ℓ-zero) : Type (ℓ-suc ℓ-zero) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag (b : Bool) (q : Q) : Type ℓ-zero where
    stop : (isAcc q Eq.≡ b) → Tag b q
    step : ⟨ Alphabet ⟩ → Tag b q

  -- TagRep : Iso Tag Bool
  -- TagRep = iso
  --   (λ { stop → false ; step → true})
  --   (λ { false → stop ; true → step})
  --   (λ { false → refl ; true → refl})
  --   (λ { stop → refl ; step → refl})

  -- isSetTag : isSet Tag
  -- isSetTag = isSetRetract (TagRep .fun) (TagRep .inv) (TagRep .leftInv) isSetBool

  TraceF : (Bool × Q) → Functor (Bool × Q)
  TraceF (b , q) = ⊕e (Tag b q) λ where
    (stop _) → k ε
    (step c) → k (literal c) ⊗e Var (b , (δ q c))

  Trace : Bool → (q : Q) → Grammar ℓ-zero
  Trace b q = μ TraceF (b , q)

  module _ where
    Ix-f : Unit → Functor (Bool × Q)
    Ix-f _ = &e Q (λ q → ⊕e (Bool) (λ b → Var (b , q)))

    Str-f : ∀ (A : _ → Grammar ℓ-zero)
      → Algebra TraceF A
      → Algebra StrF λ t → ⟦ Ix-f t ⟧ A
    Str-f A α _ = ⊕ᴰ-elim λ where
      StrTag.nil → &ᴰ-intro λ q → σ (isAcc q) ∘g α (_ , q) ∘g σ (stop Eq.refl)
      (StrTag.cons c) → &ᴰ-intro λ q →
        ⊕ᴰ-elim (λ b → σ b ∘g α (b , q) ∘g σ (step c))
        ∘g ⊕ᴰ-distR .StrongEquivalence.fun
        ∘g id ,⊗ π (δ q c)
    opaque
      unfolding ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL 
      Str-f-homo : ∀ {A B}
        → (α : Algebra TraceF A) (β : Algebra TraceF B)
        → (ϕ : Homomorphism TraceF α β)
        → isHomo StrF (Str-f _ α) (Str-f _ β) λ sᵢ → map (Ix-f sᵢ) (ϕ .fst)
      Str-f-homo α β ϕ _ = ⊕ᴰ≡ _ _ λ where
        StrTag.nil → λ i → &ᴰ-intro λ q → σ (isAcc q) ∘g ϕ .snd (_ , q) i ∘g σ (stop Eq.refl)
        (StrTag.cons c) → λ i → &ᴰ-intro λ q →
          ⊕ᴰ-elim (λ b → σ b ∘g ϕ .snd (b , q) i ∘g σ (step c))
          ∘g ⊕ᴰ-distR .StrongEquivalence.fun
          ∘g id ,⊗ π (δ q c)

  TraceStructure = mkStructure TraceF

  parseTrace : StructureTransform
    (mkStructure StrF)
    TraceStructure
  parseTrace .StructureTransform.Ix-f = Ix-f
  parseTrace .StructureTransform.Str-f = Str-f
  parseTrace .StructureTransform.Str-f-homo = Str-f-homo
