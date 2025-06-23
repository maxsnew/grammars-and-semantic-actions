{-

  A Structure is a pair of a type of indices Ix and an Ix-family of grammars.

  We use this to define a *structure transformer* which is a functor of algebras and is a "fusable" notion of a fold from one tree type to another.

-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Structure (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Indexed Alphabet

private
  variable ℓA ℓB ℓC ℓX ℓY : Level


record Structure (ℓX : Level) : Type (ℓ-suc ℓX) where
  field
    Ix : Type ℓX
    -- A syntactic representaiton of an endofunctor on Gr^Ix
    Str : Ix → Functor Ix

mkStructure : ∀ {Ix : Type ℓX} (Str : Ix → Functor Ix) → Structure ℓX
mkStructure Str = record { Ix = _ ; Str = Str }

-- A StructureTransform is a "fusable" fold over S trees producing T trees.
record StructureTransform (S : Structure ℓX) (T : Structure ℓX) : Type (ℓ-suc ℓX) where
  private
    module S = Structure S
    module T = Structure T
  field
    -- Equivalent to a functor Gr^T.Ix → Gr^S.Ix
    Ix-f  : S.Ix → Functor T.Ix
    -- a functor T-alg → S-alg over Ix-f
    -- this is the action on objects
      Str-f : ∀ (A : _ → Grammar ℓX) → Algebra T.Str A → Algebra S.Str λ sᵢ → ⟦ Ix-f sᵢ ⟧ A
    -- because Algebras are a structure, to show that Str-f extends to
    -- a functor we only need to show that it preserves the property
    -- of being a homomorphism
    Str-f-homo : ∀ {A B}
      → (α : Algebra T.Str A) (β : Algebra T.Str B)
      → (ϕ : Homomorphism T.Str α β)
      → isHomo S.Str (Str-f _ α) (Str-f _ β) λ sᵢ → map (Ix-f sᵢ) (ϕ .fst)

-- StructureTransforms satisfy the following fusion principle which
-- fuses two folds into one.
module _ {S T : Structure ℓX}{A} (F : StructureTransform S T) where
  private
    module S = Structure S
    module T = Structure T
    module F = StructureTransform F
  StructureTransform-fusion : ∀ (α : Algebra T.Str A)
    → (λ sᵢ →
        map (F.Ix-f sᵢ) (rec T.Str α)
        ∘g rec S.Str (F.Str-f _ (initialAlgebra T.Str)) sᵢ)
      ≡ rec S.Str (F.Str-f _ α)
  StructureTransform-fusion α =
    μ-η S.Str (F.Str-f A α)
      (compHomo S.Str
                (initialAlgebra S.Str)
                (F.Str-f (μ T.Str) (initialAlgebra T.Str))
                (F.Str-f A α)
        (_ , F.Str-f-homo (initialAlgebra T.Str) α (recHomo T.Str α))
        (recHomo S.Str (F.Str-f _ (initialAlgebra T.Str))))
