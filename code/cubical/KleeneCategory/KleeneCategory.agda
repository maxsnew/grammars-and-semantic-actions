module KleeneCategory.KleeneCategory where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_ ; _≤_)

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import KleeneCategory.IndexedCoproduct
open import KleeneCategory.FunctorAlgebra

module _ {ℓ ℓ' ℓS : Level}
  (K : MonoidalCategory ℓ ℓ')
  (coprods : IndexedCoproducts {ℓ}{ℓ'}{ℓS} (K .MonoidalCategory.C)) where
  open MonoidalCategory K
  open Functor
  open BinCoproduct

  bincoprod : BinCoproducts C
  bincoprod x y =
    IndexedToBinary
     (K .MonoidalCategory.C) x y
       (coprods λ z → ob-idx-by-bool {ℓ}{ℓ'}{ℓS} C x y (lower z))

  -- TODO use profunctors to define a coproduct functor?
  coprodWith : (b : ob) → Functor (MonoidalCategory.C K) (MonoidalCategory.C K)
  F-ob (coprodWith b) x = bincoprod b x .binCoprodOb
  F-hom (coprodWith b) {x}{y} f = 
    bincoprod b x .univProp
      (bincoprod b y .binCoprodInj₁)
      (f ⋆⟨ C ⟩ bincoprod b y .binCoprodInj₂) .fst .fst
  F-id (coprodWith b) {x} =
    cong
      (λ z →
        bincoprod b x .univProp
        (bincoprod b x .binCoprodInj₁)
        z .fst .fst)
      (⋆IdL (bincoprod b x .binCoprodInj₂)) ∙
    cong
      fst
      (
        bincoprod b x .univProp
        (bincoprod b x .binCoprodInj₁)
        (bincoprod b x .binCoprodInj₂)
        .snd (id , (⋆IdR _) , (⋆IdR _))
      )
  F-seq (coprodWith b) {x} {y} {z} f g =
    cong fst
      (bincoprod b x .univProp
        (bincoprod b z .binCoprodInj₁)
        (f ⋆⟨ C ⟩ g ⋆⟨ C ⟩ bincoprod b z .binCoprodInj₂) .snd
        (seq' C (F-hom (coprodWith b) f) (F-hom (coprodWith b) g) ,
          (sym (⋆Assoc _ _ _) ∙
           cong
           (λ h → h ⋆⟨ C ⟩
             bincoprod b y .univProp
               (bincoprod b z .binCoprodInj₁)
               (g ⋆⟨ C ⟩ bincoprod b z .binCoprodInj₂) .fst .fst)
             (bincoprod b x .univProp
               (bincoprod b y .binCoprodInj₁)
               (seq' C f (bincoprod b y .binCoprodInj₂)) .fst .snd .fst) ∙
           bincoprod b y .univProp
             (bincoprod b z .binCoprodInj₁)
             (seq' C g (bincoprod b z .binCoprodInj₂)) .fst .snd .fst
           ,
          (
          sym (⋆Assoc _ _ _) ∙
           cong (λ h → h ⋆⟨ C ⟩
             bincoprod b y .univProp
               (bincoprod b z .binCoprodInj₁)
               (g ⋆⟨ C ⟩ bincoprod b z .binCoprodInj₂) .fst .fst)
               (bincoprod b x .univProp
                 (bincoprod b y .binCoprodInj₁)
                 (seq' C f (bincoprod b y .binCoprodInj₂)) .fst .snd .snd)
          ) ∙
          ⋆Assoc _ _ _ ∙
          cong (λ h → f ⋆⟨ C ⟩ h)
            (bincoprod b y .univProp
              (bincoprod b z .binCoprodInj₁)
              (seq' C g (bincoprod b z .binCoprodInj₂)) .fst .snd .snd)
          ∙
          sym (⋆Assoc _ _ _)
          ))
      )
  F-Functor : (a : ob) → (b : ob) → Functor (MonoidalCategory.C K) (MonoidalCategory.C K)
  F-Functor a b = coprodWith b ∘F ─⊗─ ∘F (Constant C C a ,F Id)

  G-Functor : (a : ob) → (b : ob) → Functor (MonoidalCategory.C K) (MonoidalCategory.C K)
  G-Functor a b = coprodWith b ∘F ─⊗─ ∘F (Id ,F Constant C C a)

  open FAlgebra
  open KleeneCategory.IndexedCoproduct.IndexedCoproduct

  record KleeneCategoryStr : Type (ℓ-max (ℓ-suc ℓS) (ℓ-max ℓ ℓ')) where
    field
      M : MonoidalStr C
      distributiveL : {S : hSet ℓS} → {idx : S .fst → ob} → (x : ob) →
        CatIso C
          (x ⊗ (coprods {S} idx .coprodOb))
          (coprods {S} (λ y → x ⊗ (idx y)) .coprodOb)
      distributiveR : {S : hSet ℓS} → {idx : S .fst → ob} → (x : ob) →
        CatIso C
          ((coprods {S} idx .coprodOb) ⊗ x)
          (coprods {S} (λ y → (idx y) ⊗ x) .coprodOb)
      initialF : (a : ob) → (b : ob) → initial-algebra (F-Functor a b)
      initialG : (a : ob) → (b : ob) → initial-algebra (G-Functor a b)
      F-with-unit-iso : (a : ob) → (b : ob) →
        CatIso C
          (initialF a b .fst .carrier)
          ((initialF a unit .fst .carrier) ⊗ b)
      G-with-unit-iso : (a : ob) → (b : ob) →
        CatIso C
          (initialG a b .fst .carrier)
          (b ⊗ (initialF a unit .fst .carrier))

module _ {ℓ ℓS : Level} where
  isSetLiftedBool : isSet (Lift {ℓ-zero}{ℓS} Bool)
  isSetLiftedBool x y a b i =
    liftExt
      (isSetBool (lower (x)) (lower y)
      (cong lower a) (cong lower b) i)

  -- Kleene algebras with a poset structure are Kleene categories
  record KleeneAlgebra : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓS)) where
    field
      K : hSet ℓ
      zeroKA : K .fst
      unitKA : K .fst
      _⊕_ : K .fst → K .fst → K .fst
      _⊗_ : K .fst → K .fst → K .fst
      star : K .fst → K .fst
      ⊕assoc : (x y z : K .fst) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
      ⊕comm : (x y : K .fst) → x ⊕ y ≡ y ⊕ x
      ⊕zero : (x : K .fst) → x ⊕ zeroKA ≡ x
      ⊕idem : (x : K .fst) → x ⊕ x ≡ x
      ⊗assoc : (x y z : K .fst) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
      ⊗unitR : (x : K .fst) → x ⊗ unitKA ≡ x
      ⊗unitL : (x : K .fst) → unitKA ⊗ x ≡ x
      ⊗distL : (x y z : K .fst) → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)
      ⊗distR : (x y z : K .fst) → (y ⊕ z) ⊗ x ≡ (y ⊗ x) ⊕ (z ⊗ x)
      ⊗zeroL : (x : K .fst) → zeroKA ⊗ x ≡ zeroKA
      ⊗zeroR : (x : K .fst) → x ⊗ zeroKA ≡ zeroKA
      one-plus-starR : (x : K .fst) → (unitKA ⊕ (x ⊗ (star x))) ⊕ star x ≡ star x
      one-plus-starL : (x : K .fst) → (unitKA ⊕ ((star x) ⊗ x)) ⊕ star x ≡ star x
      star-inL : (a b x : K .fst) → (b ⊕ (a ⊗ x)) ⊕ x ≡ x → ((star a) ⊗ b) ⊕ x ≡ x
      star-inR : (a b x : K .fst) → (b ⊕ (x ⊗ a)) ⊕ x ≡ x → (b ⊗ (star a)) ⊕ x ≡ x
      -- Add axioms for infinitary ⊕
      ⊕idx : {S : hSet ℓS} → (idx : S .fst → K .fst) → K .fst
      ⊕idx-distL : {S : hSet ℓS} → (idx : S .fst → K .fst) → (x : K .fst) →
        x ⊗ (⊕idx {S} idx) ≡ ⊕idx {S} (λ y → x ⊗ (idx y))
      ⊕idx-distR : {S : hSet ℓS} → (idx : S .fst → K .fst) → (x : K .fst) →
        (⊕idx {S} idx) ⊗ x ≡ ⊕idx {S} (λ y → (idx y) ⊗ x)
      ⊕idx-inj : {S : hSet ℓS} → (idx : S .fst → K .fst) →
        (s : S .fst) → idx s ⊕ (⊕idx {S} idx) ≡ ⊕idx {S} idx
      ⊕idx-lub : {S : hSet ℓS} → (idx : S .fst → K .fst) →
        (z : K .fst) → ((s : S .fst) → idx s ⊕ z ≡ z) →
        (⊕idx {S} idx) ⊕ z ≡ z
      ⊕idx-bin :
        (x y : K .fst) →
        (idx : Lift {ℓ-zero}{ℓS} Bool → K .fst) →
        (idx (lift true) ≡ x) → (idx (lift false) ≡ y) →
        (⊕idx {Lift {ℓ-zero}{ℓS} Bool , isSetLiftedBool} idx) ≡ (x ⊕ y)

    _≤_ : K .fst → K .fst → Set ℓ
    _≤_ x y = x ⊕ y ≡ y

    open IsPoset

    KA-is-poset : IsPoset _≤_
    is-set KA-is-poset = K .snd
    is-prop-valued KA-is-poset a b x y = K .snd (a ⊕ b) b x y
    is-refl KA-is-poset x = ⊕idem x
    is-trans KA-is-poset a b c a≤b b≤c =
      cong (λ d → a ⊕ d) (sym b≤c) ∙
      sym (⊕assoc _ _ _) ∙
      cong (λ d → d ⊕ c) a≤b ∙
      b≤c
    is-antisym KA-is-poset a b a≤b b≤a =
      sym b≤a ∙
      ⊕comm _ _ ∙
      a≤b

    KA-Poset : Poset ℓ ℓ
    KA-Poset = (K .fst) , (posetstr _≤_ KA-is-poset)

    open PosetStr

    KA-Cat : Category ℓ ℓ
    KA-Cat = PosetCategory KA-Poset

    isPropHom-KA-Cat : (x y : K .fst) → isProp (KA-Cat [ x , y ])
    isPropHom-KA-Cat x y =
      KA-is-poset .is-prop-valued x y

    open MonoidalStr renaming (_⊗_ to _⊗M_)
    open TensorStr renaming (_⊗_ to _⊗T_)
    open Functor

    KA-Monoidal : MonoidalStr KA-Cat
    F-ob (─⊗─ (tenstr KA-Monoidal)) x = x .fst ⊗ x .snd
    F-hom (─⊗─ (tenstr KA-Monoidal)) {x} {y} f =
      cong (λ a → (x .fst ⊗ x .snd) ⊕ (a ⊗ y .snd)) (sym (f .fst)) ∙
      cong (λ a → (x .fst ⊗ x .snd) ⊕ ((fst x ⊕ fst y) ⊗ a)) (sym (f .snd)) ∙
      cong (λ a → (x .fst ⊗ x .snd) ⊕ a)
        (⊗distL (fst x ⊕ fst y) (snd x) (snd y)) ∙
      cong
       (λ a → (x .fst ⊗ x .snd) ⊕ (a ⊕ (((fst x ⊕ fst y) ⊗ snd y))))
         (⊗distR (snd x) (fst x) (fst y)) ∙
      cong
       (λ a → (x .fst ⊗ x .snd) ⊕ ((((fst x ⊗ snd x) ⊕ (fst y ⊗ snd x))) ⊕ a))
         (⊗distR (snd y) (fst x) (fst y)) ∙
      sym (⊕assoc (x .fst ⊗ x .snd) ((fst x ⊗ snd x) ⊕ (fst y ⊗ snd x)) ((fst x ⊗ snd y) ⊕ (fst y ⊗ snd y))) ∙
      cong (λ a → a ⊕ ((x .fst ⊗ y .snd) ⊕ (y .fst ⊗ y .snd)))
        (sym (⊕assoc (x .fst ⊗ x .snd) (x .fst ⊗ x .snd) (y .fst ⊗ x .snd))) ∙
      cong (λ a → (a ⊕ (y .fst ⊗ x .snd)) ⊕ ((x .fst ⊗ y .snd ) ⊕ (y .fst ⊗ y .snd))) (⊕idem (x .fst ⊗ x .snd)) ∙
      cong (λ a → a ⊕ ((x .fst ⊗ y .snd) ⊕ (y .fst ⊗ y .snd))) (sym (⊗distR (x .snd) (x .fst) (y .fst))) ∙
      cong (λ a → ((x .fst ⊕ y .fst) ⊗ x .snd) ⊕ a) (sym (⊗distR (y .snd) (x .fst) (y .fst))) ∙
      sym (⊗distL (x .fst ⊕ y .fst) (x .snd) (y .snd)) ∙
      cong (λ a → a ⊗ (x .snd ⊕ y .snd)) (f .fst)  ∙
      cong (λ a → y .fst ⊗ a) (f .snd)
    F-id (─⊗─ (tenstr KA-Monoidal)) =
      KA-is-poset .is-prop-valued _ _ _ _
    F-seq (─⊗─ (tenstr KA-Monoidal)) f g =
      KA-is-poset .is-prop-valued _ _ _ _
    unit (tenstr KA-Monoidal) = unitKA
    NatTrans.N-ob (NatIso.trans (α KA-Monoidal)) (x , y , z) =
      cong (λ a → a ⊕ ((x ⊗ y) ⊗ z)) (sym (⊗assoc x y z)) ∙
      ⊕idem ((x ⊗ y) ⊗ z)
    NatTrans.N-hom (NatIso.trans (α KA-Monoidal)) f =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.inv (NatIso.nIso (α KA-Monoidal) (x , y , z)) =
      cong (λ a → a ⊕ (x ⊗ (y ⊗ z))) (⊗assoc x y z) ∙
       ⊕idem (x ⊗ (y ⊗ z))
    isIso.sec (NatIso.nIso (α KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.ret (NatIso.nIso (α KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    NatTrans.N-ob (NatIso.trans (η KA-Monoidal)) x =
      cong (λ a → a ⊕ x) (⊗unitL x) ∙
      ⊕idem _
    NatTrans.N-hom (NatIso.trans (η KA-Monoidal)) f =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.inv (NatIso.nIso (η KA-Monoidal) x) =
      cong (λ a → x ⊕ a) (⊗unitL x) ∙
      ⊕idem _ ∙
      sym (⊗unitL x)
    isIso.sec (NatIso.nIso (η KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.ret (NatIso.nIso (η KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    NatTrans.N-ob (NatIso.trans (ρ KA-Monoidal)) x =
      cong (λ a → a ⊕ x) (⊗unitR x) ∙ ⊕idem _
    NatTrans.N-hom (NatIso.trans (ρ KA-Monoidal)) f =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.inv (NatIso.nIso (ρ KA-Monoidal) x) =
      cong (λ a → x ⊕ a) (⊗unitR x) ∙ ⊕idem _ ∙ sym (⊗unitR x)
    isIso.sec (NatIso.nIso (ρ KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    isIso.ret (NatIso.nIso (ρ KA-Monoidal) x) =
      KA-is-poset .is-prop-valued _ _ _ _
    pentagon KA-Monoidal w x y z =
      KA-is-poset .is-prop-valued _ _ _ _
    triangle KA-Monoidal x y =
      KA-is-poset .is-prop-valued _ _ _ _

    KA-MonoidalCat : MonoidalCategory ℓ ℓ
    MonoidalCategory.C KA-MonoidalCat = KA-Cat
    MonoidalCategory.monstr KA-MonoidalCat = KA-Monoidal

    open KleeneCategory.IndexedCoproduct.IndexedCoproduct

    KA-Cat-has-IndexedCoproducts : IndexedCoproducts {ℓ}{ℓ}{ℓS} KA-Cat
    coprodOb (KA-Cat-has-IndexedCoproducts {S} IdxObjs) =
      ⊕idx {S} IdxObjs
    iₛ (KA-Cat-has-IndexedCoproducts IdxObjs) s =
      ⊕idx-inj IdxObjs s
    fst (fst (univprop (KA-Cat-has-IndexedCoproducts IdxObjs) {z} f)) =
      ⊕idx-lub IdxObjs z f
    snd (fst (univprop (KA-Cat-has-IndexedCoproducts IdxObjs) f)) s =
     KA-is-poset .is-prop-valued _ _ _ _
    snd (univprop (KA-Cat-has-IndexedCoproducts IdxObjs) f) y =
      Σ≡Prop
      (λ x → isPropΠ λ s → KA-Cat .Category.isSetHom
        ((KA-Cat Category.⋆ iₛ (KA-Cat-has-IndexedCoproducts IdxObjs) s) x)
        (f s))
      (KA-is-poset .is-prop-valued _ _ _ _)

    open KleeneCategoryStr
    open isIso

    KA-has-KleeneCatStr : KleeneCategoryStr KA-MonoidalCat KA-Cat-has-IndexedCoproducts
    M KA-has-KleeneCatStr = KA-MonoidalCat .MonoidalCategory.monstr
    fst (distributiveL KA-has-KleeneCatStr {S}{idx} x) =
      cong (λ a → ((x ⊗ (⊕idx idx)) ⊕ a)) (sym (⊕idx-distL {S} idx x)) ∙
      ⊕idem (x ⊗ ⊕idx idx) ∙
      ⊕idx-distL {S} idx x
    inv (snd (distributiveL KA-has-KleeneCatStr {S}{idx} x)) =
      cong (λ a → a ⊕ (x ⊗ (⊕idx idx))) (sym (⊕idx-distL {S} idx x)) ∙
      ⊕idem _
    sec (snd (distributiveL KA-has-KleeneCatStr x)) =
      KA-is-poset .is-prop-valued _ _ _ _ 
    ret (snd (distributiveL KA-has-KleeneCatStr x)) =
      KA-is-poset .is-prop-valued _ _ _ _
    fst (distributiveR KA-has-KleeneCatStr {S}{idx} x) =
      cong
        (λ a → a ⊕ ⊕idx λ y → idx y ⊗ x)
        (⊕idx-distR {S} idx x) ∙
      ⊕idem _
    inv (snd (distributiveR KA-has-KleeneCatStr {S}{idx} x)) =
      cong (λ a → a ⊕ ((⊕idx idx) ⊗ x)) (sym (⊕idx-distR {S} idx x)) ∙
      (⊕idem _)
    sec (snd (distributiveR KA-has-KleeneCatStr x)) =
      KA-is-poset .is-prop-valued _ _ _ _
    ret (snd (distributiveR KA-has-KleeneCatStr x)) =
      KA-is-poset .is-prop-valued _ _ _ _
    FAlgebra.carrier (fst (initialF KA-has-KleeneCatStr a b)) =
      (star a) ⊗ b
    FAlgebra.algebra (fst (initialF KA-has-KleeneCatStr a b)) =
      cong
        (λ c → c ⊕ (star a ⊗ b))
        (⊕idx-bin b (a ⊗ (star a ⊗ b)) _ refl refl) ∙
      cong (λ c → (b ⊕ c) ⊕ (star a ⊗ b)) (sym (⊗assoc a (star a) b)) ∙
      cong (λ c → (c ⊕ ((a ⊗ star a) ⊗ b)) ⊕ (star a ⊗ b))  (sym (⊗unitL b)) ∙
      cong (λ c → c ⊕ (star a ⊗ b)) (sym (⊗distR b unitKA (a ⊗ star a))) ∙
      sym (⊗distR b (unitKA ⊕ (a ⊗ star a)) (star a)) ∙
      cong (λ c → c ⊗ b) (one-plus-starR a)
    fst (fst (snd (initialF KA-has-KleeneCatStr a b) y)) =
      star-inL a b
        (y .FAlgebra.carrier)
        (cong (λ c → c ⊕ y .FAlgebra.carrier)
          (sym (⊕idx-bin b (a ⊗ y .FAlgebra.carrier) _ refl refl)) ∙ y .FAlgebra.algebra)
    snd (fst (snd (initialF KA-has-KleeneCatStr a b) y)) =
      KA-is-poset .is-prop-valued _ _ _ _
    snd (snd (initialF KA-has-KleeneCatStr a b) y) z =
      Σ≡Prop
        (λ x → KA-Cat .Category.isSetHom _ _)
        (KA-is-poset .is-prop-valued _ _ _ _)
    FAlgebra.carrier (fst (initialG KA-has-KleeneCatStr a b)) =
      b ⊗ (star a)
    FAlgebra.algebra (fst (initialG KA-has-KleeneCatStr a b)) =
      cong (λ c → c ⊕ (b ⊗ star a)) (⊕idx-bin b ((b ⊗ star a) ⊗ a) _ refl refl) ∙
      cong (λ c → (b ⊕ c) ⊕ (b ⊗ star a)) (⊗assoc b (star a) a) ∙
      cong (λ c → (c ⊕ (b ⊗ (star a ⊗ a))) ⊕ (b ⊗ star a)) (sym (⊗unitR b)) ∙
      cong (λ c → c ⊕ (b ⊗ star a)) (sym (⊗distL b unitKA (star a ⊗ a))) ∙
      sym (⊗distL b (unitKA ⊕ (star a ⊗ a)) (star a)) ∙
      cong (λ c → b ⊗ c) (one-plus-starL a)
    fst (fst (snd (initialG KA-has-KleeneCatStr a b) y)) =
      star-inR a b
        (y .FAlgebra.carrier)
        (cong (λ c → c ⊕ y .FAlgebra.carrier)
          (sym (⊕idx-bin b (y .FAlgebra.carrier ⊗ a) _ refl refl)) ∙ y .FAlgebra.algebra)
    snd (fst (snd (initialG KA-has-KleeneCatStr a b) y)) =
      KA-is-poset .is-prop-valued _ _ _ _
    snd (snd (initialG KA-has-KleeneCatStr a b) y) z =
      Σ≡Prop
        (λ x → KA-Cat .Category.isSetHom _ _)
        (KA-is-poset .is-prop-valued _ _ _ _)
    fst (F-with-unit-iso KA-has-KleeneCatStr a b) =
      cong (λ c → (c ⊗ b) ⊕ ((star a ⊗ unitKA) ⊗ b)) (sym (⊗unitR (star a))) ∙
      ⊕idem _
    inv (snd (F-with-unit-iso KA-has-KleeneCatStr a b)) =
      cong (λ c → (c ⊗ b) ⊕ (star a ⊗ b)) (⊗unitR (star a)) ∙
      ⊕idem _
    sec (snd (F-with-unit-iso KA-has-KleeneCatStr a b)) =
      KA-is-poset .is-prop-valued _ _ _ _
    ret (snd (F-with-unit-iso KA-has-KleeneCatStr a b)) =
      KA-is-poset .is-prop-valued _ _ _ _
    fst (G-with-unit-iso KA-has-KleeneCatStr a b) =
      cong (λ c → (b ⊗ c) ⊕ (b ⊗ (star a ⊗ unitKA))) (sym (⊗unitR (star a))) ∙
      ⊕idem _
    inv (snd (G-with-unit-iso KA-has-KleeneCatStr a b)) =
      cong (λ c → (b ⊗ c) ⊕ (b ⊗ star a)) (⊗unitR (star a)) ∙
      ⊕idem _
    sec (snd (G-with-unit-iso KA-has-KleeneCatStr a b)) =
      KA-is-poset .is-prop-valued _ _ _ _
    ret (snd (G-with-unit-iso KA-has-KleeneCatStr a b)) =
      KA-is-poset .is-prop-valued _ _ _ _
