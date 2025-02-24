{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Helper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function.More

open import Cubical.Functions.Embedding

open import Cubical.Relation.Binary.Order.Loset
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.More using (DecΣ ; Fin≡SumFin ; Fin≃Finℕ ; Fin≃SumFin)
import Cubical.Data.FinData as FD

import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.Bool as Bool hiding (_⊕_; _≤_)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
import Cubical.Data.Fin as Fin
import Cubical.Data.Fin.Arithmetic as Arith
import Cubical.Data.Equality as Eq
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable ℓ ℓ' : Level

open import Cubical.Relation.Nullary.DecidablePropositions.More public
open import Cubical.Relation.Nullary.DecidablePropositions.Powerset.Base
open import Cubical.Foundations.HLevels.MoreMore public
open import Cubical.Data.FinSet.More public

open Iso

subCardBounded :
  ∀ {ℓ ℓ'} (A : FinSet ℓ) (DecProp'B : ⟨ A ⟩ → DecProp' ℓ') →
  card (_ , isFinSetSub A DecProp'B) ≤ card A
subCardBounded A DecProp'B = card↪Inequality
  (_ , isFinSetSub A DecProp'B) A
  ∣ fst , (λ w x → isEmbeddingFstΣProp (λ a → isDecProp→isProp (str (DecProp'B a))) {w} {x}) ∣₁

-- module _
--   {ℓ ℓ'} {A : Type ℓ}
--   (isFinSetA : isFinSet A)
--   (_≺_ : A → A → Type ℓ')
--   (isDecProp≺ : (x y : A) → isDecProp (x ≺ y))
--   (isLoset≺ : IsLoset _≺_) where

--   private
--     FinSetA : FinSet ℓ
--     FinSetA = A , isFinSetA

--     _DecProp'≺_ : (x y : A) → DecProp' ℓ'
--     x DecProp'≺ y = x ≺ y , isDecProp≺ x y

--     module isLoset≺ = IsLoset isLoset≺

--     LowerFinSet : (a : A) → FinSet (ℓ-max ℓ ℓ')
--     LowerFinSet a = _ , isFinSetSub FinSetA (_DecProp'≺ a)

--     ExceptFinSet : (exception : A) → FinSet ℓ
--     ExceptFinSet exception =
--       let is-exception : A → DecProp ℓ
--           is-exception a = ((_ , isFinSet→isSet isFinSetA exception a) , isFinSet→Discrete isFinSetA exception a) in
--       _ , isFinSetSub FinSetA (DecProp→DecProp' ∘ negateDecProp ∘ is-exception)

--     exceptEquiv : (exception : A) → ⟨ ExceptFinSet exception ⟩ ⊎ ⊤ ≃ A
--     exceptEquiv exception = isoToEquiv (iso f g sec ret)
--       where
--       f : ⟨ ExceptFinSet exception ⟩ ⊎ ⊤ → A
--       f = Sum.rec fst (const exception)

--       g : A → ⟨ ExceptFinSet exception ⟩ ⊎ ⊤
--       g a = decRec (const (inr tt)) (λ ¬exception≡a → inl (a , ¬exception≡a)) (isFinSet→Discrete isFinSetA exception a)

--       sec : (a : A) → f (g a) ≡ a
--       sec a with (isFinSet→Discrete isFinSetA exception a)
--       ... | yes p = p
--       ... | no ¬p = refl

--       ret : (b : ⟨ ExceptFinSet exception ⟩ ⊎ ⊤) → g (f b) ≡ b
--       ret (inl a) with (isFinSet→Discrete isFinSetA exception (a .fst))
--       ... | yes p = ⊥.rec (a .snd p)
--       ... | no ¬p = cong inl (Σ≡Prop (λ _ → isProp¬ _) refl)
--       ret (inr tt) with (isFinSet→Discrete isFinSetA exception exception)
--       ... | yes p = refl
--       ... | no ¬p = ⊥.rec (¬p refl)

--     cardExcept : (exception : A) → suc (card (ExceptFinSet exception)) ≡ card FinSetA
--     cardExcept exception =
--       +-comm 1 (card (ExceptFinSet exception))
--       ∙ sym (card+ (ExceptFinSet exception) (⊤ , isFinSet⊤))
--       ∙ cardEquiv (_ , isFinSet⊎ (ExceptFinSet exception) (⊤ , isFinSet⊤)) FinSetA ∣ exceptEquiv exception ∣₁

--     Lower↪Except : (a : A) → ⟨ LowerFinSet a ⟩ ↪ ⟨ ExceptFinSet a ⟩
--     Lower↪Except a .fst = λ (x , x≺a) → x , λ a≡x → isLoset≺.is-irrefl _ (subst (λ a → x ≺ a) a≡x x≺a)
--     Lower↪Except a .snd = injEmbedding
--       (isFinSet→isSet (str (ExceptFinSet a)))
--       (λ p → Σ≡Prop (λ _ → isLoset≺.is-prop-valued _ _) (PathPΣ p .fst))

--     rankBounded : (a : A) → card (LowerFinSet a) < card FinSetA
--     rankBounded a = ≤<-trans
--       (card↪Inequality (LowerFinSet a) (ExceptFinSet a) ∣ Lower↪Except a ∣₁)
--       (0 , cardExcept a)

--   rank : (a : A) → Fin (card FinSetA)
--   rank a = enum (card (LowerFinSet a)) (rankBounded a)

--   rankedAt : Fin (card FinSetA) → A
--   rankedAt k = {!!}

--   rankEquiv : A ≃ Fin (card FinSetA)
--   rankEquiv = isoToEquiv (iso rank rankedAt sec ret)
--     where
--     sec : ∀ k → rank (rankedAt k) ≡ k
--     sec k = {!!}

--     ret : ∀ a → rankedAt (rank a) ≡ a
--     ret a = {!!}

--   isFinSet→isFinOrd : isFinOrd A
--   isFinSet→isFinOrd = card FinSetA , rankEquiv

isFinSetFin' : ∀ {n} → isFinSet (FD.Fin n)
isFinSetFin' = isFinSetFin & subst isFinSet (sym Fin≡SumFin)

isContr→isFinOrd : ∀ {ℓ} → {A : Type ℓ} →
  isContr A → isFinOrd A
isContr→isFinOrd isContrA = 1 , isContr→Equiv isContrA isContrSumFin1

DecProp'→isFinOrd :
  ∀ {ℓ} → (A : DecProp' ℓ) → isFinOrd (A .fst)
DecProp'→isFinOrd (u , true , u≃⊤) =
  EquivPresIsFinOrd
    (invEquiv u≃⊤)
    (isContr→isFinOrd isContrUnit)
DecProp'→isFinOrd (u , false , u≃⊥) =
  EquivPresIsFinOrd
    (invEquiv u≃⊥)
    isFinOrd⊥
