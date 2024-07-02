module Semantics.Grammar.KleeneStar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper
open import Semantics.String
open import Semantics.Grammar.Base
open import Semantics.Grammar.LinearProduct
open import Semantics.Grammar.Empty

private
  variable
    ℓG : Level
    Σ₀ : Type ℓ-zero

data KL* (g : Grammar {Σ₀} ℓG) : Grammar ℓG
  where
  nil : ε-grammar ⊢ (KL* g)
  cons : g ⊗ KL* g ⊢ KL* g

  -- -- Use IW trees to prove that Kleene star forms a set
  -- -- (provided that the original grammar outputs sets)
  -- module isSetKL*TyProof
  --   (hg : hGrammar)
  --   where
  --   g = hg .fst
  --   setParses = hg .snd

  --   KL*Ty-X = String

  --   KL*Ty-S : KL*Ty-X → Type ℓ
  --   KL*Ty-S w =
  --     (w ≡ []) ⊎
  --     (Σ[ s ∈ Splitting w ] g (s .fst .fst))

  --   KL*Ty-P : ∀ w → KL*Ty-S w → Type ℓ-zero
  --   KL*Ty-P w (inl x) = ⊥
  --   KL*Ty-P w (inr x) = ⊤

  --   KL*Ty-inX : ∀ w (s : KL*Ty-S w) → KL*Ty-P w s → KL*Ty-X
  --   KL*Ty-inX w (inr (s , sp)) x = s .fst .snd

  --   KL*Ty→W : ∀ {w} → KL*Ty g w → IW KL*Ty-S KL*Ty-P KL*Ty-inX w
  --   KL*Ty→W (nil x) = node (inl x) λ ()
  --   KL*Ty→W (cons x) =
  --     node (inr ((x .fst) , (x .snd .fst)))
  --       λ _ → KL*Ty→W (x .snd .snd)

  --   W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
  --   W→KL*Ty (node (inl x) subtree) = nil x
  --   W→KL*Ty (node (inr x) subtree) =
  --     cons ((x .fst) , ((x .snd) , (W→KL*Ty (subtree _))))

  --   KL*TyRetractofW :
  --     ∀ {w} (p : KL*Ty g w) →
  --     W→KL*Ty (KL*Ty→W p) ≡ p
  --   KL*TyRetractofW (nil x) = refl
  --   KL*TyRetractofW (cons x) =
  --     cong cons
  --       (ΣPathP (refl ,
  --         (ΣPathP (refl ,
  --           (KL*TyRetractofW (x .snd .snd))))))


  --   isSetKL*Ty-S : ∀ w → isSet (KL*Ty-S w)
  --   isSetKL*Ty-S w =
  --     isSet⊎
  --       (isGroupoidString _ _)
  --       (isSetΣ (isSetSplitting _) λ _ → setParses _)

  --   isSetKL*Ty : ∀ w → isSet (KL*Ty g w)
  --   isSetKL*Ty w =
  --     isSetRetract
  --       KL*Ty→W W→KL*Ty
  --       KL*TyRetractofW
  --       (isOfHLevelSuc-IW 1 isSetKL*Ty-S w)

  -- open isSetKL*TyProof
  -- KL* : Grammar → Grammar
  -- KL* g w = KL*Ty g w

  -- isHGrammar-KL* : (g : hGrammar) → isHGrammar (KL* (g .fst))
  -- isHGrammar-KL* g _ = isSetKL*Ty g _
