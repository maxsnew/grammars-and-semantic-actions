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
    Ix-f₀ : singl {A = S.Ix → _} (λ s → ⟦ Ix-f s ⟧)
    Ix-f₁ : singlP
      (λ i → ∀ (sᵢ : S.Ix) → {A B : T.Ix → Grammar ℓX} →
        ((x : T.Ix) → Term (A x) (B x)) →
        Term (Ix-f₀ .snd i sᵢ A) (Ix-f₀ .snd i sᵢ B))
      λ sᵢ → map (Ix-f sᵢ)
    -- a functor T-alg → S-alg over Ix-f
    -- this is the action on objects
    Str-f : ∀ (A : _ → Grammar ℓX) → Algebra T.Str A → Algebra S.Str λ sᵢ → Ix-f₀ .fst sᵢ A
    -- because Algebras are a structure, to show that Str-f extends to
    -- a functor we only need to show that it preserves the property
    -- of being a homomorphism
    Str-f-homo : ∀ {A B}
      → (α : Algebra T.Str A) (β : Algebra T.Str B)
      → (ϕ : Homomorphism T.Str α β)
      → isHomo S.Str (Str-f _ α) (Str-f _ β) λ sᵢ → Ix-f₁ .fst sᵢ (ϕ .fst)

-- StructureTransforms satisfy the following fusion principle which
-- fuses two folds into one.
module _ {S T : Structure ℓX}{A} (F : StructureTransform S T) where
  private
    module S = Structure S
    module T = Structure T
    module F = StructureTransform F
  StructureTransform-fusion : ∀ (α : Algebra T.Str A)
    → (λ sᵢ →
        F.Ix-f₁ .fst sᵢ (rec T.Str α)
        ∘g rec S.Str (F.Str-f _ (initialAlgebra T.Str)) sᵢ)
      ≡ rec S.Str (F.Str-f _ α)
  StructureTransform-fusion α = μ-η S.Str (F.Str-f A α)
    (compHomo S.Str
      (initialAlgebra S.Str)
      (F.Str-f (μ T.Str) (initialAlgebra T.Str))
      (F.Str-f A α)
      (_ , F.Str-f-homo (initialAlgebra T.Str) α (recHomo T.Str α))
      (recHomo S.Str (F.Str-f _ (initialAlgebra T.Str))))

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
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Ix-f = Ix-f
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Ix-f₀ = _ , refl
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Ix-f₁ = _ , refl
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Str-f = Str-f
mkStructureTransform Ix-f Str-f Str-f-homo .StructureTransform.Str-f-homo = Str-f-homo

idStrTrans : ∀ {S : Structure ℓX} → StructureTransform S S
idStrTrans = mkStructureTransform retF (λ A α → α) λ _ _ ϕ → ϕ .snd

_∘str_ : ∀ {S T U : Structure ℓX}
  → StructureTransform T U
  → StructureTransform S T
  → StructureTransform S U
(G^ ∘str F^) .Ix-f = F^ .Ix-f >=>F G^ .Ix-f
(G^ ∘str F^) .Ix-f₀ .fst = λ sᵢ A → F^ .Ix-f₀ .fst sᵢ (λ tⱼ → G^ .Ix-f₀ .fst tⱼ A)
(G^ ∘str F^) .Ix-f₀ .snd = funExt λ sᵢ →
  ⟦⟧>>= (F^ .Ix-f sᵢ) (G^ .Ix-f)
  ∙ (λ i A → F^ .Ix-f₀ .snd i sᵢ λ tⱼ → G^ .Ix-f₀ .snd i tⱼ A)
(G^ ∘str F^) .Ix-f₁ .fst sᵢ f = F^ .Ix-f₁ .fst sᵢ (λ tⱼ → G^ .Ix-f₁ .fst tⱼ f)
 -- TODO: proof by induction
_∘str_ {ℓX = ℓX}{U = U}G^ F^ .Ix-f₁ .snd =
  funExt λ sᵢ → compPathP' {B = λ Ix-f → ∀ {A B : Ix U → Grammar _} → ((x : Ix U) → A x ⊢ B x) → Ix-f A ⊢ Ix-f B}
    {p = ⟦⟧>>= (F^ .Ix-f sᵢ) (G^ .Ix-f)}
    {q = (λ i A → F^ .Ix-f₀ .snd i sᵢ λ tⱼ → G^ .Ix-f₀ .snd i tⱼ A)}
  (map>>= (F^ .Ix-f sᵢ) (G^ .Ix-f))
  λ i f → F^ .Ix-f₁ .snd i sᵢ (λ tⱼ → G^ .Ix-f₁ .snd i tⱼ f)
(G^ ∘str F^) .Str-f A α = F^ .Str-f _ (Str-f G^ _ α)
(G^ ∘str F^) .Str-f-homo α β ϕ sᵢ =
  F^ .Str-f-homo _ _ (_ , (G^ .Str-f-homo α β ϕ)) sᵢ
