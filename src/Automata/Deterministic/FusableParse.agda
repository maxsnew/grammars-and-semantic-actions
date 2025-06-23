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

open import Grammar Alphabet
open import Parser Alphabet
open import Term Alphabet
open import Grammar.Inductive.Structure Alphabet

private
  variable
    ℓ ℓ' : Level

record DeterministicAutomaton (Q : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    init : Q
    isAcc : Q → Bool
    δ : Q → ⟨ Alphabet ⟩ → Q

  data Tag (b : Bool) (q : Q) : Type ℓ where
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
    (stop _) → k ε*
    (step c) → k (literal* c) ⊗e Var (b , (δ q c))

  Trace : Bool → (q : Q) → Grammar ℓ
  Trace b q = μ TraceF (b , q)

  module _ where
    StrF : Unit* {ℓ} → Functor (Unit* {ℓ})
    StrF _ = *Ty (LiftG _ char) _
  
    Ix-f : Unit* {ℓ} → Functor (Bool × Q)
    Ix-f _ = &e Q (λ q → ⊕e (Lift Bool) (λ (lift b) → Var (b , q)))

    Str-f : ∀ (A : _ → Grammar ℓ) → Algebra TraceF A → Algebra (λ _ → *Ty (LiftG _ char) _) λ t → ⟦ Ix-f t ⟧ A -- λ sᵢ → ⟦ Ix-f sᵢ ⟧ A
    Str-f A α _ = 
      ⊕ᴰ-elim (λ where
      *Tag.nil  → &ᴰ-intro λ q → σ _ ∘g liftG ∘g α (_ , q) ∘g σ (stop Eq.refl)
      *Tag.cons → &ᴰ-intro λ q →
        (⊕ᴰ-elim λ c → (⊕ᴰ-elim λ b → σ _ ∘g liftG ∘g α (lower b , q) ∘g σ (step c) ∘g (liftG ∘g liftG) ,⊗ id )
          ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ π (δ q c))
        ∘g ⊕ᴰ-distL .StrongEquivalence.fun
        ∘g (lowerG ∘g lowerG) ,⊗ lowerG)

    opaque
      unfolding ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL 
      Str-f-homo : ∀ {A B}
        → (α : Algebra TraceF A) (β : Algebra TraceF B)
        → (ϕ : Homomorphism TraceF α β)
        → isHomo StrF (Str-f _ α) (Str-f _ β) λ sᵢ → map (Ix-f sᵢ) (ϕ .fst)
      Str-f-homo α β ϕ _ = ⊕ᴰ≡ _ _ (λ where
        *Tag.nil  → λ i → &ᴰ-intro λ q → σ _ ∘g liftG ∘g ϕ .snd (_ , q) i ∘g σ (stop Eq.refl)
        *Tag.cons → λ i → &ᴰ-intro λ q →
          (⊕ᴰ-elim λ c → (⊕ᴰ-elim λ b → σ _ ∘g liftG ∘g ϕ .snd (lower b , q) i ∘g σ (step c) ∘g (liftG ∘g liftG) ,⊗ id )
            ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g id ,⊗ π (δ q c))
          ∘g ⊕ᴰ-distL .StrongEquivalence.fun
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG)

  parseTrace : StructureTransform
    (mkStructure (λ _ → *Ty (LiftG _ char) _))
    (mkStructure TraceF)
  parseTrace .StructureTransform.Ix-f = Ix-f
  parseTrace .StructureTransform.Str-f = Str-f
  parseTrace .StructureTransform.Str-f-homo = Str-f-homo
