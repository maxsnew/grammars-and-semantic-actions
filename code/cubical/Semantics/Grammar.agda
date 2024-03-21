{-# OPTIONS  #-}
module Semantics.Grammar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma

private
  variable ℓ ℓ' : Level

-- TODO : cubical upstream?
negateDecProp : ∀ {ℓ} → DecProp ℓ → DecProp ℓ
fst (fst (negateDecProp A)) = ¬ A .fst .fst
snd (fst (negateDecProp A)) = isProp→ isProp⊥
snd (negateDecProp A) =
  decRec
    (λ a → no (λ x → x a))
    (λ ¬a → yes ¬a)
    (A .snd)

doubleNegDecProp :
  ∀ {ℓ} (A : DecProp ℓ) →
  negateDecProp (negateDecProp A) .fst .fst →
  A .fst .fst
doubleNegDecProp A x =
  decRec
  (λ a → a)
  (λ ¬a → ⊥.elim (x ¬a))
  (A .snd)

module GrammarDefs ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w =
    isSetΣ (isSet× isSetString isSetString)
      λ s → isGroupoidString w (s .fst ++ s .snd)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → hSet ℓ

  open ListPath
  ILin : Grammar
  ILin w = (w ≡ []) , isGroupoidString w []

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w =
    (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × g' (s .fst .snd) .fst) ,
    isSetΣ (isSetSplitting w) λ s →
      isSet× (g (s .fst .fst) .snd) (g' (s .fst .snd) .snd)

  literal : (Σ₀ .fst) → Grammar
  literal c w = ([ c ] ≡ w) , isGroupoidString ([ c ]) w

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w =
    (∀ (w' : String) → g w' .fst → g' (w' ++ w) .fst) ,
    isSetΠ (λ w' → isSetΠ λ p → g' (w' ++ w) .snd)

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w =
    (∀ (w' : String) → g (w ++ w') .fst → g' w' .fst) ,
     isSetΠ (λ w' → isSetΠ (λ p → g' w' .snd))

  ΠLin : {A : hSet ℓ} → (A .fst → Grammar) → Grammar
  ΠLin {A} f w = (∀ (a : A .fst) → f a w .fst) , isSetΠ λ a → f a w .snd

  ΣLin : {A : hSet ℓ} → (A .fst → Grammar) → Grammar
  ΣLin {A} f w =
    (Σ[ a ∈ A .fst ] f a w .fst) ,
      isSetΣ (A .snd) λ a → f a w .snd

  ⊤Lin : Grammar
  ⊤Lin w = Unit* , isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = (g w .fst × g' w .fst) ,
    isSet× (g w .snd) (g' w .snd)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = (g w .fst ⊎ g' w .fst) ,
    isSet⊎ (g w .snd) (g' w .snd)

  ⊥Lin : Grammar
  ⊥Lin w = Lift ⊥ ,
    λ x y a b i →
      liftExt (isProp→isSet isProp⊥ (lower x) (lower y)
        (cong lower a) (cong lower b) i)

  _⇒_ : Grammar → Grammar → Grammar
  (g ⇒ g') w =
    (g w .fst → g' w .fst) ,
    isSetΠ (λ p → g' w .snd)

  ParseTransformer : Grammar → Grammar → Type ℓ
  ParseTransformer g g' = ∀ {w} → g w .fst → g' w .fst

  -- Recall that a parse transformer is the shallow
  -- embedding of a term from the syntax
  --
  -- So we can embed some inference rules
  --
  module _ (g : Grammar) where

    idPT : ParseTransformer g g
    idPT x = x

    id-⊗ : ParseTransformer ILin (g -⊗ g)
    id-⊗ {w'} pI w gw =
      transport
        (cong (λ a → g a .fst)
          (sym (++-unit-r w) ∙
          cong (λ a → w ++ a) (sym pI) ))
        gw

    ⊗appPT : ParseTransformer (g ⊗ (g -⊗ g)) g
    ⊗appPT x =
      transport
        (sym (cong (λ b → g b .fst) (x .fst .snd)))
        (x .snd .snd (fst (fst (x .fst))) (x .snd .fst))

  isEquivalentGrammar : Grammar → Grammar → Type ℓ
  isEquivalentGrammar g g' = ∀ {w} → Iso (g w .fst) (g' w .fst)

  module _ (g : Grammar) where
    open Iso
    ILin⊗g→g : ParseTransformer (ILin ⊗ g) g
    ILin⊗g→g {w} p =
      transport
        (cong (λ a → g a .fst) (
          cong (λ a → a ++ (p .fst .fst .snd)) (sym (p .snd .fst)) ∙
          sym (p .fst .snd)))
        (p .snd .snd)

    g→ILin⊗g : ParseTransformer g (ILin ⊗ g)
    g→ILin⊗g {w} p = (([] , _) , refl) , (refl , p)

    -- ILinUnitL : isEquivalentGrammar (ILin ⊗ g) g
    -- fun (ILinUnitL) = ILin⊗g→g
    -- inv (ILinUnitL) = g→ILin⊗g
    -- rightInv (ILinUnitL {w}) b = {!!}
    -- leftInv ILinUnitL a = {!!}

    g⊗ILin→g : ParseTransformer (g ⊗ ILin) g
    g⊗ILin→g {w} p =
      transport
        (cong (λ a → g a .fst)
          ((sym (++-unit-r _) ∙
            cong (λ a → (p .fst .fst .fst ++ a)) (sym (p .snd .snd))) ∙
            sym (p .fst .snd) ))
        (p .snd .fst)

    g→g⊗ILin : ParseTransformer g (g ⊗ ILin)
    g→g⊗ILin {w} p = ((w , []) , (sym (++-unit-r _))) , (p , refl)

    -- ILinUnitR : isEquivalentGrammar (g ⊗ ILin) g
    -- fun (ILinUnitR) = {!!}
    -- inv (ILinUnitR) = {!!}
    -- rightInv (ILinUnitR) = {!!}
    -- leftInv (ILinUnitR) = {!!}

  data KL*Ty (g : Grammar) : (w : String) → Type ℓ where
    nil : (KL*Ty g [])
    cons :
      ∀ {w w'} →
        g w .fst → KL*Ty g w' → KL*Ty g (w ++ w')

  module isSetKL*TyProof (g : Grammar) where
    KL*Ty-X = String

    KL*Ty-S : KL*Ty-X → Type ℓ
    KL*Ty-S w =
      (w ≡ []) ⊎
      (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst)

    KL*Ty-P : ∀ w → KL*Ty-S w → Type ℓ-zero
    KL*Ty-P w (inl x) = ⊥
    KL*Ty-P w (fsuc x) = ⊤

    KL*Ty-inX : ∀ w (s : KL*Ty-S w) → KL*Ty-P w s → KL*Ty-X
    KL*Ty-inX w (fsuc (s , sp)) x = s .fst .snd


    KL*Ty→W : ∀ {w} → KL*Ty g w → IW KL*Ty-S KL*Ty-P KL*Ty-inX w
    KL*Ty→W nil = node (inl refl) (λ ())
    KL*Ty→W (cons {w}{w'} x p) =
      node (fsuc (((w , w') , refl) , x)) λ _ → KL*Ty→W p

    W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
    W→KL*Ty (node (inl x) subtree) =
      transport
        (cong (λ a → KL*Ty g a) (sym x))
        (KL*Ty.nil {g = g})
    W→KL*Ty (node (fsuc x) subtree) =
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
        (isSetΣ
          (isSetSplitting _)
          λ s → g (s .fst .fst) .snd
        )

    isSetKL*Ty : ∀ w → isSet (KL*Ty g w)
    isSetKL*Ty w =
      isSetRetract
        KL*Ty→W W→KL*Ty
        KL*TyRetractofW
        (isOfHLevelSuc-IW 1 isSetKL*Ty-S w)

  open isSetKL*TyProof
  KL* : Grammar → Grammar
  KL* g w = KL*Ty g w , isSetKL*Ty _ _

  ⊕Σ₀ : Grammar
  ⊕Σ₀ w =
    (Σ[ c ∈ Σ₀ .fst ] literal c w .fst) ,
    isSetΣ (Σ₀ .snd) (λ c → literal c w .snd)

  String→KL* : (w : String) → KL* ⊕Σ₀ w .fst
  String→KL* [] = nil
  String→KL* (c ∷ w) =
    cons (c , refl) (String→KL* w)

  fold*r :
    (g h : Grammar) →
    ParseTransformer ILin h →
    ParseTransformer (g ⊗ h) h →
    ParseTransformer (KL* g) h
  fold*r g h pε p⊗ nil = pε refl
  fold*r g h pε p⊗ (cons {w}{w'} x g*parse) =
    p⊗
      (((w , w') , refl) ,
       (x , (fold*r g h pε p⊗ g*parse)))

  fold*l :
    (g h : Grammar) →
    ParseTransformer ILin h →
    ParseTransformer (h ⊗ g) h →
    ParseTransformer (KL* g) h
  fold*l g h pε p⊗ g*parse =
    fold*r
      g
      (h -⊗ h)
      (id-⊗ h)
      the-cons-step
      g*parse
      []
      (pε refl)
    where
    -⊗intro-and-sub-PT : ParseTransformer ((h ⊗ g) ⊗ (h -⊗ h)) h
    -⊗intro-and-sub-PT x =
      ⊗appPT h
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
    ILinReg : RegularGrammar
    _⊗Reg_ : RegularGrammar → RegularGrammar → RegularGrammar
    literalReg : (Σ₀ .fst) → RegularGrammar
    _⊕Reg_ : RegularGrammar → RegularGrammar → RegularGrammar
    KL*Reg : RegularGrammar → RegularGrammar

  RegularGrammar→Grammar : RegularGrammar → Grammar
  RegularGrammar→Grammar ILinReg = ILin
  RegularGrammar→Grammar (g ⊗Reg g') =
    (RegularGrammar→Grammar g) ⊗ (RegularGrammar→Grammar g')
  RegularGrammar→Grammar (literalReg c) = literal c
  RegularGrammar→Grammar (g ⊕Reg g') =
    RegularGrammar→Grammar g ⊕ RegularGrammar→Grammar g'
  RegularGrammar→Grammar (KL*Reg g) = KL* (RegularGrammar→Grammar g)
