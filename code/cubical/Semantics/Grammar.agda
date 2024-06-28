module Semantics.Grammar where

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

open import Semantics.Helper public
open import Semantics.String public

private
  variable ℓG ℓΣ₀ : Level

module GrammarDefs ℓG ((Σ₀' , isFinSetΣ₀') : FinSet ℓΣ₀) where
  private
    ℓ : Level
    ℓ = ℓ-max ℓG ℓΣ₀

  Σ₀rename : FinSet ℓ
  Σ₀rename = (Lift {ℓΣ₀}{ℓ} Σ₀' , isFinSetLift isFinSetΣ₀')

  Σ₀ : Type ℓ
  Σ₀ = Σ₀rename .fst

  isFinSetΣ₀ : isFinSet Σ₀
  isFinSetΣ₀ = Σ₀rename .snd

  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → Type ℓ

  isHGrammar : Grammar → Type ℓ
  isHGrammar g = ∀ w → isSet (g w)

  hGrammar : Type (ℓ-suc ℓ)
  hGrammar = Σ[ g ∈ Grammar ] isHGrammar g

  ε-grammar : Grammar
  ε-grammar w = w ≡ []

  LiftGrammar : ∀ {L} → Grammar → String → Type (ℓ-max (ℓ-suc ℓ) L)
  LiftGrammar {L} g w = Lift {ℓ}{ℓ-max (ℓ-suc ℓ) L} (g w)

  isHGrammar-ε-grammar : isHGrammar ε-grammar
  isHGrammar-ε-grammar _ = isGroupoidString _ _

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)
  infixr 20 _⊗_

  isHGrammar-⊗ : (g g' : hGrammar) → isHGrammar (g .fst ⊗ g' .fst)
  isHGrammar-⊗ g g' _ =
    isSetΣ (isSetSplitting _) (λ s → isSet× (g .snd _) (g' .snd _))

  literal : Σ₀ → Grammar
  literal c w = w ≡ [ c ]

  isHGrammar-literal : ∀ c → isHGrammar (literal c)
  isHGrammar-literal c w = isGroupoidString _ _

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w = ∀ (w' : String) → g w' → g' (w' ++ w)

  isHGrammar--⊗ : (g g' : hGrammar) → isHGrammar (g .fst -⊗ g' .fst)
  isHGrammar--⊗ g g' _ = isSetΠ (λ _ → isSetΠ (λ _ → g' .snd _))

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w = ∀ (w' : String) → g' w' → g (w ++ w')

  isHGrammar-⊗- : (g g' : hGrammar) → isHGrammar (g .fst ⊗- g' .fst)
  isHGrammar-⊗- g g' _ = isSetΠ λ _ → isSetΠ (λ _ → g .snd _)

  LinearΠ : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΠ {A} f w = ∀ (a : A) → f a w

  isHGrammar-LinearΠ :
    {A : hSet ℓ} → (B : A .fst → hGrammar) →
    isHGrammar (LinearΠ {A .fst} (λ a → B a .fst))
  isHGrammar-LinearΠ {A} B _ = isSetΠ (λ a → B a .snd _)

  LinearΣ : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΣ {A} f w = Σ[ a ∈ A ] f a w

  LinearΣ-syntax : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΣ-syntax = LinearΣ

  syntax LinearΣ-syntax {A} (λ x → B) = LinΣ[ x ∈ A ] B

  isHGrammar-LinearΣ :
    {A : hSet ℓ} → (B : A .fst → hGrammar) →
    isHGrammar (LinearΣ {A .fst} (λ a → B a .fst))
  isHGrammar-LinearΣ {A} B _ = isSetΣ (A .snd) (λ a → B a .snd _)

  ⊤-grammar : Grammar
  ⊤-grammar _ = Unit*

  isHGrammar-⊤-grammar : isHGrammar ⊤-grammar
  isHGrammar-⊤-grammar _ = isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = g w × g' w

  isHGrammar-& :
    (g : hGrammar) → (g' : hGrammar) → isHGrammar (g .fst & g' .fst)
  isHGrammar-& g g' _ = isSet× (g .snd _) (g' .snd _)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = g w ⊎ g' w

  isHGrammar-⊕ :
    (g : hGrammar) → (g' : hGrammar) → isHGrammar (g .fst ⊕ g' .fst)
  isHGrammar-⊕ g g' _ = isSet⊎ (g .snd _) (g' .snd _)

  ⊥-grammar : Grammar
  ⊥-grammar _ = Lift ⊥

  isHGrammar-⊥-grammar : isHGrammar ⊥-grammar
  isHGrammar-⊥-grammar _ = isProp→isSet isProp⊥*

  DecProp-grammar' :
    DecProp ℓ → Grammar
  DecProp-grammar' d =
    decRec (λ _ → ⊤-grammar) (λ _ → ⊥-grammar) (d .snd)

  _⇒_ : Grammar → Grammar → Grammar
  (g ⇒ g') w = g w → g' w

  isHGrammar-⇒ :
    {g : Grammar} → (g' : hGrammar) → isHGrammar ( g ⇒ g' .fst )
  isHGrammar-⇒ g' _ = isSet→ (g' .snd _)

  Term : Grammar → Grammar → Type ℓ
  Term g g' = ∀ {w} → g w → g' w

  infix 5 Term
  syntax Term g g' = g ⊢ g'


  data KL*Ty (g : Grammar) : (w : String) → Type ℓ where
    nil : Term ε-grammar (KL*Ty g)
    cons : Term (g ⊗ KL*Ty g) (KL*Ty g)

  -- Use IW trees to prove that Kleene star forms a set
  -- (provided that the original grammar outputs sets)
  module isSetKL*TyProof
    (hg : hGrammar)
    where
    g = hg .fst
    setParses = hg .snd

    KL*Ty-X = String

    KL*Ty-S : KL*Ty-X → Type ℓ
    KL*Ty-S w =
      (w ≡ []) ⊎
      (Σ[ s ∈ Splitting w ] g (s .fst .fst))

    KL*Ty-P : ∀ w → KL*Ty-S w → Type ℓ-zero
    KL*Ty-P w (inl x) = ⊥
    KL*Ty-P w (inr x) = ⊤

    KL*Ty-inX : ∀ w (s : KL*Ty-S w) → KL*Ty-P w s → KL*Ty-X
    KL*Ty-inX w (inr (s , sp)) x = s .fst .snd

    KL*Ty→W : ∀ {w} → KL*Ty g w → IW KL*Ty-S KL*Ty-P KL*Ty-inX w
    KL*Ty→W (nil x) = node (inl x) λ ()
    KL*Ty→W (cons x) =
      node (inr ((x .fst) , (x .snd .fst)))
        λ _ → KL*Ty→W (x .snd .snd)

    W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
    W→KL*Ty (node (inl x) subtree) = nil x
    W→KL*Ty (node (inr x) subtree) =
      cons ((x .fst) , ((x .snd) , (W→KL*Ty (subtree _))))

    KL*TyRetractofW :
      ∀ {w} (p : KL*Ty g w) →
      W→KL*Ty (KL*Ty→W p) ≡ p
    KL*TyRetractofW (nil x) = refl
    KL*TyRetractofW (cons x) =
      cong cons
        (ΣPathP (refl ,
          (ΣPathP (refl ,
            (KL*TyRetractofW (x .snd .snd))))))


    isSetKL*Ty-S : ∀ w → isSet (KL*Ty-S w)
    isSetKL*Ty-S w =
      isSet⊎
        (isGroupoidString _ _)
        (isSetΣ (isSetSplitting _) λ _ → setParses _)

    isSetKL*Ty : ∀ w → isSet (KL*Ty g w)
    isSetKL*Ty w =
      isSetRetract
        KL*Ty→W W→KL*Ty
        KL*TyRetractofW
        (isOfHLevelSuc-IW 1 isSetKL*Ty-S w)

  open isSetKL*TyProof
  KL* : Grammar → Grammar
  KL* g w = KL*Ty g w

  isHGrammar-KL* : (g : hGrammar) → isHGrammar (KL* (g .fst))
  isHGrammar-KL* g _ = isSetKL*Ty g _

  ⊕Σ₀ : Grammar
  ⊕Σ₀ w = Σ[ c ∈ Σ₀ ] literal c w

  isHGrammar-⊕Σ₀ : isHGrammar ⊕Σ₀
  isHGrammar-⊕Σ₀ _ = isSetΣ isSetΣ₀ (λ _ → isHGrammar-literal _ _)

  MaybeGrammar : Grammar → Grammar
  MaybeGrammar g = g ⊕ ⊤-grammar

  String→KL* : (w : String) → KL* ⊕Σ₀ w
  String→KL* [] = nil refl
  String→KL* (c ∷ w) =
    cons ((([ c ] , w) , refl) , ((c , refl) , (String→KL* w)))

  KL*→String : ∀ {w} → KL* ⊕Σ₀ w → String
  KL*→String {w} p = w

  ∥_∥grammar : Grammar → Grammar
  ∥_∥grammar g w = ∥ g w ∥₁

  isPropValuedGrammar : (g : Grammar) → Type ℓ
  isPropValuedGrammar g = ∀ {w} → isProp (g w)

  isPropValuedGrammar-literal : ∀ {c} → isPropValuedGrammar (literal c)
  isPropValuedGrammar-literal {c} = isSetString _ [ c ]

  isPropValuedGrammar-ε-grammar : isPropValuedGrammar ε-grammar
  isPropValuedGrammar-ε-grammar = isSetString _ []

  data RegularExpression : Type ℓ where
    ε-Reg : RegularExpression
    _⊗Reg_ : RegularExpression → RegularExpression → RegularExpression
    literalReg : Σ₀ → RegularExpression
    _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
    KL*Reg : RegularExpression → RegularExpression

  RegularExpression→Grammar : RegularExpression → Grammar
  RegularExpression→Grammar ε-Reg = ε-grammar
  RegularExpression→Grammar (g ⊗Reg g') =
    (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
  RegularExpression→Grammar (literalReg c) = literal c
  RegularExpression→Grammar (g ⊕Reg g') =
    RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
  RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

  Language : Grammar → Type ℓ
  Language g = Σ[ w ∈ String ] ∥ g w ∥₁

  isSetLanguage : (g : hGrammar) → isSet (Language (g .fst))
  isSetLanguage g = isSetΣ isSetString (λ w → isProp→isSet isPropPropTrunc)

  module _ (g g' : Grammar) where
    isLogicallyEquivalent : Type ℓ
    isLogicallyEquivalent = Term g g' × Term g' g

    isWeaklyEquivalent : Type ℓ
    isWeaklyEquivalent = Iso (Language g) (Language g')

    open Iso
    isLogicalEquivalence→WeakEquivalence :
      isLogicallyEquivalent → isWeaklyEquivalent
    fst (fun (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
    snd (fun (isLogicalEquivalence→WeakEquivalence logEq) x) =
      PT.rec
        isPropPropTrunc
        (λ p → ∣ logEq .fst p ∣₁)
        (x .snd)
    fst (inv (isLogicalEquivalence→WeakEquivalence logEq) x) = x .fst
    snd (inv (isLogicalEquivalence→WeakEquivalence logEq) x) =
      PT.rec
        isPropPropTrunc
        (λ p → ∣ logEq .snd p ∣₁)
        (x .snd)
    rightInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
      Σ≡Prop (λ _ → isPropPropTrunc) refl
    leftInv (isLogicalEquivalence→WeakEquivalence logEq) _ =
      Σ≡Prop (λ _ → isPropPropTrunc) refl

    isStronglyEquivalent : Type ℓ
    isStronglyEquivalent = ∀ w → Iso (g w) (g' w)

    isStronglyEquivalent→isWeaklyEquivalent :
      isStronglyEquivalent → isWeaklyEquivalent
    fst (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
    snd (fun (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
      PT.rec
        isPropPropTrunc
        (λ p → ∣ strEq (x .fst) .fun p ∣₁)
        (x .snd)
    fst (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) = x .fst
    snd (inv (isStronglyEquivalent→isWeaklyEquivalent strEq) x) =
      PT.rec
        isPropPropTrunc
        (λ p → ∣ strEq (x .fst) .inv p ∣₁)
        (x .snd)
    rightInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
      Σ≡Prop (λ _ → isPropPropTrunc) refl
    leftInv (isStronglyEquivalent→isWeaklyEquivalent strEq) _ =
      Σ≡Prop (λ _ → isPropPropTrunc) refl
