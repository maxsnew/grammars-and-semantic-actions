{-

  A Structure is a pair of a type of indices Ix and an Ix-family of grammars.

  We use this to define a *structure transformer* which is a functor of algebras and is a "fusable" notion of a fold from one tree type to another.

-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Liftless.Structure (Alphabet : hSet ℓ-zero)where

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

open import Grammar.Inductive.Liftless.Indexed Alphabet

private
  variable ℓA ℓB ℓC ℓX ℓY : Level


record Structure (ℓX : Level) : Type (ℓ-suc ℓX) where
  field
    Ix : Type ℓX
    -- A syntactic representation of an endofunctor on Gr^Ix
    Str : Ix → Functor Ix

mkStructure : ∀ {Ix : Type ℓX} (Str : Ix → Functor Ix) → Structure ℓX
mkStructure Str = record { Ix = _ ; Str = Str }

-- A StructureTransform is a "fusable" fold over S trees producing T trees.
-- Note: I think I made this overly complicated.

record StructureTransform (S : Structure ℓX) (T : Structure ℓX) : Type (ℓ-suc ℓX) where
  private
    module S = Structure S
    module T = Structure T
  field
    -- A functor Gr^T.Ix → Gr^S.Ix
    Ix-f₀  : (T.Ix → Grammar ℓX) → (S.Ix → Grammar ℓX)
    Ix-f₁  : ∀ {A B : T.Ix → Grammar ℓX} →
        ((x : T.Ix) → Term (A x) (B x)) →
        (sᵢ : S.Ix) → 
        Term (Ix-f₀ A sᵢ) (Ix-f₀ B sᵢ)

    -- a functor T-alg → S-alg over Ix-f
    -- this is the action on objects
    Str-f : ∀ (A : _ → Grammar ℓX) → Algebra T.Str A → Algebra S.Str (Ix-f₀ A)
    -- because Algebras are a structure, to show that Str-f extends to
    -- a functor we only need to show that it preserves the property
    -- of being a homomorphism
    Str-f-homo : ∀ {A B}
      → (α : Algebra T.Str A) (β : Algebra T.Str B)
      → (ϕ : Homomorphism T.Str α β)
      → isHomo S.Str (Str-f _ α) (Str-f _ β) (Ix-f₁ (ϕ .fst))

  -- A structure transform gives a way of expressing a fold from S.Str
  -- given a T.Str algebra
  toFold :
    ∀ {A} (α : Algebra T.Str A)
    → ∀ s → μ S.Str s ⊢ Ix-f₀ A s
  toFold α s = rec S.Str (Str-f _ α) s

  toFoldToTrees : ∀ s → μ S.Str s ⊢ Ix-f₀ (μ T.Str) s
  toFoldToTrees = toFold (initialAlgebra T.Str)

  -- The functoriality conditions ensure that the following fusion principle holds
  toFold-fusion :
    ∀ {A}(α : Algebra T.Str A)
    → (λ sᵢ →
        Ix-f₁ (rec T.Str α) sᵢ
        ∘g toFoldToTrees sᵢ)
      ≡ toFold α
  toFold-fusion α = μ-η S.Str (Str-f _ α)
    (compHomo S.Str
      (initialAlgebra S.Str)
      (Str-f (μ T.Str) (initialAlgebra T.Str))
      (Str-f _ α)
      (_ , Str-f-homo (initialAlgebra T.Str) α (recHomo T.Str α))
      (recHomo S.Str (Str-f _ (initialAlgebra T.Str))))

open Structure
open StructureTransform

mkStructureTransform : ∀ {S T : Structure ℓX}
  (Ix-f : S .Ix → Functor (T .Ix))
  → (Str-f : ∀ (A : _ → Grammar ℓX) → Algebra (T .Str) A → Algebra (S .Str) λ sᵢ → ⟦ Ix-f sᵢ ⟧ A)
  → (Str-f-homo :
    ∀ {A B}
      → (α : Algebra (T .Str) A) (β : Algebra (T .Str) B)
      → (ϕ : Homomorphism (T .Str) α β)
      → isHomo (S .Str) (Str-f _ α) (Str-f _ β) λ sᵢ → map (Ix-f sᵢ) (ϕ .fst))
  → StructureTransform S T
mkStructureTransform Ix-f Str-f Str-f-homo .Ix-f₀ A sᵢ = ⟦ Ix-f sᵢ ⟧ A
mkStructureTransform Ix-f Str-f Str-f-homo .Ix-f₁ t sᵢ = map (Ix-f sᵢ) t
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Str-f = Str-f
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Str-f-homo = Str-f-homo

idStrTrans : ∀ {S : Structure ℓX} → StructureTransform S S
idStrTrans = mkStructureTransform retF (λ A α → α) λ _ _ ϕ → ϕ .snd

_∘str_ : ∀ {S T U : Structure ℓX}
  → StructureTransform T U
  → StructureTransform S T
  → StructureTransform S U
(G^ ∘str F^) .Ix-f₀ A = F^ .Ix-f₀ (G^ .Ix-f₀ A)
(G^ ∘str F^) .Ix-f₁ f = F^ .Ix-f₁ (G^ .Ix-f₁ f)
(G^ ∘str F^) .Str-f A α = F^ .Str-f _ (Str-f G^ _ α)
(G^ ∘str F^) .Str-f-homo α β ϕ sᵢ =
  F^ .Str-f-homo _ _ (_ , (G^ .Str-f-homo α β ϕ)) sᵢ
