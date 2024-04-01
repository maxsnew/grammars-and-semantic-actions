module Semantics.Grammar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper public
open import Semantics.String public

private
  variable ℓ ℓ' : Level

module GrammarDefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → Type ℓ

  ParsesAreSets : Grammar → Type ℓ
  ParsesAreSets g = ∀ w → isSet (g w)

  hGrammar : Type (ℓ-suc ℓ)
  hGrammar = Σ[ g ∈ Grammar ] ParsesAreSets g

  ε-grammar : Grammar
  ε-grammar w = w ≡ []

  ParsesAreSets-ε-grammar : ParsesAreSets ε-grammar
  ParsesAreSets-ε-grammar _ = isGroupoidString _ _

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)

  ParsesAreSets-⊗ : (g g' : hGrammar) → ParsesAreSets (g .fst ⊗ g' .fst)
  ParsesAreSets-⊗ g g' _ =
    isSetΣ (isSetSplitting _) (λ s → isSet× (g .snd _) (g' .snd _))

  literal : Σ₀ → Grammar
  literal c w = w ≡ [ c ]

  ParsesAreSets-literal : ∀ c → ParsesAreSets (literal c)
  ParsesAreSets-literal c w = isGroupoidString _ _

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w = ∀ (w' : String) → g w' → g' (w' ++ w)

  ParsesAreSets--⊗ : (g g' : hGrammar) → ParsesAreSets (g .fst -⊗ g' .fst)
  ParsesAreSets--⊗ g g' _ = isSetΠ (λ _ → isSetΠ (λ _ → g' .snd _))

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w = ∀ (w' : String) → g (w ++ w') → g' w'

  ParsesAreSets-⊗- : (g g' : hGrammar) → ParsesAreSets (g .fst ⊗- g' .fst)
  ParsesAreSets-⊗- g g' _ = isSetΠ (λ _ → isSetΠ (λ _ → g' .snd _))

  LinearΠ : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΠ {A} f w = ∀ (a : A) → f a w

  ParsesAreSets-LinearΠ :
    {A : hSet ℓ} → (B : A .fst → hGrammar) →
    ParsesAreSets (LinearΠ {A .fst} (λ a → B a .fst))
  ParsesAreSets-LinearΠ {A} B _ = isSetΠ (λ a → B a .snd _)

  LinearΣ : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΣ {A} f w = Σ[ a ∈ A ] f a w

  LinearΣ-syntax : {A : Type ℓ} → (A → Grammar) → Grammar
  LinearΣ-syntax = LinearΣ

  syntax LinearΣ-syntax {A} (λ x → B) = LinΣ[ x ∈ A ] B

  ParsesAreSets-LinearΣ :
    {A : hSet ℓ} → (B : A .fst → hGrammar) →
    ParsesAreSets (LinearΣ {A .fst} (λ a → B a .fst))
  ParsesAreSets-LinearΣ {A} B _ = isSetΣ (A .snd) (λ a → B a .snd _)

  ⊤-grammar : Grammar
  ⊤-grammar _ = Unit*

  ParsesAreSets-⊤-grammar : ParsesAreSets ⊤-grammar
  ParsesAreSets-⊤-grammar _ = isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = g w × g' w

  ParsesAreSets-& :
    (g : hGrammar) → (g' : hGrammar) → ParsesAreSets (g .fst & g' .fst)
  ParsesAreSets-& g g' _ = isSet× (g .snd _) (g' .snd _)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = g w ⊎ g' w

  ParsesAreSets-⊕ :
    (g : hGrammar) → (g' : hGrammar) → ParsesAreSets (g .fst ⊕ g' .fst)
  ParsesAreSets-⊕ g g' _ = isSet⊎ (g .snd _) (g' .snd _)

  ⊥-grammar : Grammar
  ⊥-grammar _ = Lift ⊥

  ParsesAreSets-⊥-grammar : ParsesAreSets ⊥-grammar
  ParsesAreSets-⊥-grammar _ = isProp→isSet isProp⊥*

  DecProp-grammar :
    DecProp ℓ → Grammar → Grammar → Grammar
  DecProp-grammar d ifyes ifno =
    decRec (λ _ → ifyes) (λ _ → ifno) (d .snd)

  -- TODO naming
  DecProp-grammar-yes-path :
    (d : DecProp ℓ) → (ifyes : Grammar) →
    (ifno : Grammar) →
    d .fst .fst → (w : String) →
    DecProp-grammar d ifyes ifno w ≡ ifyes w
  DecProp-grammar-yes-path (fst₁ , yes p) ifyes ifno x w =
    refl
  DecProp-grammar-yes-path (fst₁ , no ¬p) ifyes ifno x w =
    ⊥.rec (¬p x)

  DecProp-grammar-yes :
    (d : DecProp ℓ) → (ifyes : Grammar) →
    (ifno : Grammar) → d .fst .fst → (w : String) → ifyes w →
    DecProp-grammar d ifyes ifno w
  DecProp-grammar-yes d ifyes ifno y w x =
    transport (sym (DecProp-grammar-yes-path d ifyes ifno y w)) x

  DecProp-grammar-no-path :
    (d : DecProp ℓ) → (ifyes : Grammar) →
    (ifno : Grammar) →
    (d .fst .fst → ⊥) → (w : String) →
    DecProp-grammar d ifyes ifno w ≡ ifno w
  DecProp-grammar-no-path (fst₁ , yes p) ifyes ifno x w =
    ⊥.rec (x p)
  DecProp-grammar-no-path (fst₁ , no ¬p) ifyes ifno x w =
    refl

  DecProp-grammar-no :
    (d : DecProp ℓ) → (ifyes : Grammar) →
    (ifno : Grammar) → (d .fst .fst → ⊥) → (w : String) → ifno w →
    DecProp-grammar d ifyes ifno w
  DecProp-grammar-no d ifyes ifno y w x =
    transport (sym (DecProp-grammar-no-path d ifyes ifno y w)) x

  elimSimpleDecProp-grammar :
    (d : DecProp ℓ) → (w : String) →
    (DecProp-grammar d ⊤-grammar ⊥-grammar w) →
    d .fst .fst
  elimSimpleDecProp-grammar (fst₁ , yes p) w x = p

  -- Meant to be the exponential in the type theory
  _⇒_ : Grammar → Grammar → Grammar
  (g ⇒ g') w = g w → g' w

  ParsesAreSets-⇒ :
    {g : Grammar} → (g' : hGrammar) → ParsesAreSets ( g ⇒ g' .fst )
  ParsesAreSets-⇒ g' _ = isSet→ (g' .snd _)

  ParseTransformer : Grammar → Grammar → Type ℓ
  ParseTransformer g g' = ∀ {w} → g w → g' w

  -- TODO can I do this with parse transformers?
  data KL*Ty (g : Grammar) : (w : String) → Type ℓ where
    nil : (KL*Ty g [])
    cons :
      ∀ {w w'} →
        g w → KL*Ty g w' → KL*Ty g (w ++ w')

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
    KL*Ty→W nil = node (inl refl) (λ ())
    KL*Ty→W (cons {w}{w'} x p) =
      node (inr (((w , w') , refl) , x)) λ _ → KL*Ty→W p

    W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
    W→KL*Ty (node (inl x) subtree) =
      transport
        (cong (λ a → KL*Ty g a) (sym x))
        (KL*Ty.nil {g = g})
    W→KL*Ty (node (inr x) subtree) =
      transport
      (cong (λ a → KL*Ty g a) (sym (x .fst .snd)))
      (KL*Ty.cons {g = g} (x .snd) (W→KL*Ty (subtree _)))

    KL*TyRetractofW :
      ∀ {w} (p : KL*Ty g w) →
      W→KL*Ty (KL*Ty→W p) ≡ p
    KL*TyRetractofW nil = transportRefl (KL*Ty.nil {g = g})
    KL*TyRetractofW (cons x p) =
      transportRefl (cons x (W→KL*Ty (KL*Ty→W p))) ∙
      cong (λ a → cons x a) (KL*TyRetractofW p)

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

  ParsesAreSets-KL* : (g : hGrammar) → ParsesAreSets (KL* (g .fst))
  ParsesAreSets-KL* g _ = isSetKL*Ty g _

  ⊕Σ₀ : Grammar
  ⊕Σ₀ w = Σ[ c ∈ Σ₀ ] literal c w

  ParsesAreSets-⊕Σ₀ : ParsesAreSets ⊕Σ₀
  ParsesAreSets-⊕Σ₀ _ = isSetΣ isSetΣ₀ (λ _ → ParsesAreSets-literal _ _)

  String→KL* : (w : String) → KL* ⊕Σ₀ w
  String→KL* [] = nil
  String→KL* (c ∷ w) =
    cons (c , refl) (String→KL* w)

  stepLiteral : ∀ {w}{g : Grammar} → {c : Σ₀ } → g w → ( literal c ⊗ g ) (c ∷ w)
  stepLiteral {w} {c = c} p = splitChar c w , refl , p

  -- TODO better name
  literalSplit : ∀ c w g →
    (literal c ⊗ g) w → Σ[ w' ∈ fiber (λ a → c ∷ a) w ] g (w' .fst)
  literalSplit c [] g p =
    ⊥.rec
      (¬nil≡cons (p .fst .snd ∙
        ( cong (λ a → a ++ p .fst .fst .snd) (p .snd .fst))))
  literalSplit c (c' ∷ w) g p =
    (w , (cong (λ z → z ∷ w) c≡c')) , transport (cong g p₁₁₂≡w) (p .snd .snd)
    where
    the-string-path =
      (cong (λ z → z ++ p .fst .fst .snd) (sym (p .snd .fst)) ∙
        (sym (p .fst .snd)))

    c≡c' : c ≡ c'
    c≡c' = cons-inj₁ the-string-path

    p₁₁₂≡w : p .fst .fst .snd ≡ w
    p₁₁₂≡w = cons-inj₂ the-string-path

  -- Recall that a parse transformer is the shallow
  -- embedding of a term from the syntax
  --
  -- So we can embed some inference rules where parse transformers
  -- from g to g' correspond to judgements like
  -- x : g ⊢ M : g'
  module _ (g : Grammar) where
    id-PT : ParseTransformer g g
    id-PT x = x

    -- linear identity function
    id-⊗-PT : ParseTransformer ε-grammar (g -⊗ g)
    id-⊗-PT {w'} pI w gw =
      transport
        (cong (λ a → g a)
          (sym (++-unit-r w) ∙
          cong (λ a → w ++ a) (sym pI) ))
        gw

    ⊗appL-PT : ParseTransformer (g ⊗ (g -⊗ g)) g
    ⊗appL-PT x =
      transport
        (sym (cong g (x .fst .snd)))
        (x .snd .snd (x .fst .fst .fst) (x .snd .fst))

    module _
      (h : Grammar)
      where

      fold*r :
        ParseTransformer ε-grammar h →
        ParseTransformer (g ⊗ h) h →
        ParseTransformer (KL* g) h
      fold*r pε p⊗ nil = pε refl
      fold*r pε p⊗ (cons {w}{w'} x g*parse) =
        p⊗
          (((w , w') , refl) ,
           (x , (fold*r pε p⊗ g*parse)))
  module _
    (g : Grammar)
    (h : Grammar)
    where

    fold*l :
      ParseTransformer ε-grammar h →
      ParseTransformer (h ⊗ g) h →
      ParseTransformer (KL* g) h
    fold*l pε p⊗ g*parse =
      fold*r
        g
        (h -⊗ h)
        (id-⊗-PT h)
        the-cons-step
        g*parse
        []
        (pε refl)
      where
      -⊗intro-and-sub-PT : ParseTransformer ((h ⊗ g) ⊗ (h -⊗ h)) h
      -⊗intro-and-sub-PT x =
        ⊗appL-PT h
          ((((fst x .fst .fst) , (fst x .fst .snd)) , (x .fst .snd)) ,
          ((p⊗ (x .snd .fst)) , (x .snd .snd)))
      the-cons-step : ParseTransformer (g ⊗ (h -⊗ h)) (h -⊗ h)
      the-cons-step {w'} f w hw =
        -⊗intro-and-sub-PT
          (((w ++ fst f .fst .fst , fst f .fst .snd) ,
          cong (λ b → w ++ b) (f .fst .snd) ∙
          sym (++-assoc w (f .fst .fst .fst) (fst f .fst .snd))) ,
          ((((w , fst f .fst .fst) , refl) ,
          hw , (f .snd .fst)) ,
          f .snd .snd))

  data RegularGrammar : Type ℓ where
    ε-Reg : RegularGrammar
    _⊗Reg_ : RegularGrammar → RegularGrammar → RegularGrammar
    literalReg : Σ₀ → RegularGrammar
    _⊕Reg_ : RegularGrammar → RegularGrammar → RegularGrammar
    KL*Reg : RegularGrammar → RegularGrammar

  RegularGrammar→Grammar : RegularGrammar → Grammar
  RegularGrammar→Grammar ε-Reg = ε-grammar
  RegularGrammar→Grammar (g ⊗Reg g') =
    (RegularGrammar→Grammar g) ⊗ (RegularGrammar→Grammar g')
  RegularGrammar→Grammar (literalReg c) = literal c
  RegularGrammar→Grammar (g ⊕Reg g') =
    RegularGrammar→Grammar g ⊕ RegularGrammar→Grammar g'
  RegularGrammar→Grammar (KL*Reg g) = KL* (RegularGrammar→Grammar g)

  Language : Grammar → Type ℓ
  Language g = Σ[ w ∈ String ] ∥ g w ∥₁

  isSetLanguage : (g : hGrammar) → isSet (Language (g .fst))
  isSetLanguage g = isSetΣ isSetString (λ w → isProp→isSet isPropPropTrunc)

  module _ (g g' : Grammar) where

    isLogicallyEquivalent : Type ℓ
    isLogicallyEquivalent = ParseTransformer g g' × ParseTransformer g' g

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
