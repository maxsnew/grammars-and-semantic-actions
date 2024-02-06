module KleeneCategory where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import IndexedCoproduct
open import FunctorAlgebra

module _ {ℓ ℓ' : Level} (K : MonoidalCategory ℓ ℓ') (bincoprod : BinCoproducts (K .MonoidalCategory.C)) where
  open MonoidalCategory K
  open Functor
  open BinCoproduct

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
  F-seq (coprodWith b) {x}{y}{z} f g = {!!}

  F-Functor : (a : ob) → (b : ob) → Functor (MonoidalCategory.C K) (MonoidalCategory.C K)
  F-Functor a b = coprodWith b ∘F ─⊗─ ∘F (Constant C C a ,F Id)

  G-Functor : (a : ob) → (b : ob) → Functor (MonoidalCategory.C K) (MonoidalCategory.C K)
  G-Functor a b = coprodWith b ∘F ─⊗─ ∘F (Id ,F Constant C C a)

  open FAlgebra

  record KleeneCategoryStr : Type (ℓ-max ℓ ℓ') where
    field
      M : MonoidalStr C
      distributiveL : (x y z : ob) →
        CatIso C
        (x ⊗ (bincoprod y z .binCoprodOb))
        (bincoprod (x ⊗ y) (x ⊗ z) .binCoprodOb)
      distributiveR : (x y z : ob) →
        CatIso C ((bincoprod y z .binCoprodOb) ⊗ x) (bincoprod (y ⊗ x) (z ⊗ x) .binCoprodOb)
      initialF : (a : ob) → (b : ob) → initial-algebra (F-Functor a b)
      initialG : (a : ob) → (b : ob) → initial-algebra (G-Functor a b)
      F-with-unit-iso : (a : ob) → (b : ob) →
        CatIso C
          (initialF a b .fst .carrier)
          (b ⊗ (initialF a unit .fst .carrier))
      G-with-unit-iso : (a : ob) → (b : ob) →
        CatIso C
          (initialG a b .fst .carrier)
          ((initialF a unit .fst .carrier) ⊗ b)

module _ {ℓ : Level} where
  record KleeneAlgebra : Type (ℓ-suc ℓ) where
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
    -- TODO rearrange and factor
      {!!} ∙
      {!!} ∙
      {!!}
    F-id (─⊗─ (tenstr KA-Monoidal)) = {!!}
    F-seq (─⊗─ (tenstr KA-Monoidal)) = {!!}
    unit (tenstr KA-Monoidal) = zeroKA
    α KA-Monoidal = {!!}
    η KA-Monoidal = {!!}
    ρ KA-Monoidal = {!!}
    pentagon KA-Monoidal = {!!}
    triangle KA-Monoidal = {!!}

    KA-MonoidalCat : MonoidalCategory ℓ ℓ
    MonoidalCategory.C KA-MonoidalCat = KA-Cat
    MonoidalCategory.monstr KA-MonoidalCat = KA-Monoidal

    open BinCoproduct

    KA-Cat-BinCoproducts : BinCoproducts KA-Cat
    binCoprodOb (KA-Cat-BinCoproducts x y) = x ⊕ y
    binCoprodInj₁ (KA-Cat-BinCoproducts x y) =
      sym (⊕assoc x x y) ∙
      cong (λ a → a ⊕ y) (⊕idem x)
    binCoprodInj₂ (KA-Cat-BinCoproducts x y) =
     sym (⊕assoc y x y) ∙
      cong (λ a → a ⊕ y) (⊕comm y x) ∙
      ⊕assoc x y y ∙
      cong (λ a → x ⊕ a) (⊕idem y)
    fst (fst (univProp (KA-Cat-BinCoproducts x y) {z} f g)) =
      cong (λ a → (x ⊕ y) ⊕ a) (sym (⊕idem z)) ∙
      sym (⊕assoc (x ⊕ y) z z) ∙
      cong (λ a → a ⊕ z) (⊕assoc x y z) ∙
      cong (λ a → (x ⊕ a) ⊕ z) g ∙
      ⊕assoc x z z ∙
      cong (λ a → x ⊕ a) (⊕idem z) ∙
      f
    fst (snd (fst (univProp (KA-Cat-BinCoproducts x y) f g))) =
      KA-is-poset .is-prop-valued x _
      ((KA-Cat Category.⋆ binCoprodInj₁ (KA-Cat-BinCoproducts x y))
        (fst (fst (univProp (KA-Cat-BinCoproducts x y) f g)))) f
    snd (snd (fst (univProp (KA-Cat-BinCoproducts x y) f g))) =
      KA-is-poset .is-prop-valued y _
      ((KA-Cat Category.⋆ binCoprodInj₂ (KA-Cat-BinCoproducts x y))
      (fst (fst (univProp (KA-Cat-BinCoproducts x y) f g)))) g
    snd (univProp (KA-Cat-BinCoproducts x y) f g) z =
     Σ≡Prop
       (λ u →
         isProp×
           (KA-Cat .Category.isSetHom
             ((KA-Cat Category.⋆ binCoprodInj₁
               (KA-Cat-BinCoproducts x y)) u) f)
           (KA-Cat .Category.isSetHom
             ((KA-Cat Category.⋆ binCoprodInj₂
              (KA-Cat-BinCoproducts x y)) u) g)
        )
       (KA-is-poset .is-prop-valued (x ⊕ y) _
         (fst (univProp (KA-Cat-BinCoproducts x y) f g) .fst)
         (z .fst))

    open KleeneCategoryStr
    open isIso
    KA-has-KleeneCatStr : KleeneCategoryStr KA-MonoidalCat KA-Cat-BinCoproducts
    M KA-has-KleeneCatStr = KA-MonoidalCat .MonoidalCategory.monstr
    fst (distributiveL KA-has-KleeneCatStr x y z) =
      cong (λ a → (a ⊕ ((x ⊗ y) ⊕ (x ⊗ z)))) (⊗distL x y z) ∙
      ⊕idem ((x ⊗ y) ⊕ (x ⊗ z))
    inv (snd (distributiveL KA-has-KleeneCatStr x y z)) =
      cong (λ a → a ⊕ (x ⊗ (y ⊕ z))) (sym (⊗distL x y z)) ∙
      ⊕idem (x ⊗ (y ⊕ z))
    sec (snd (distributiveL KA-has-KleeneCatStr x y z)) =
      isPropHom-KA-Cat
        ((x ⊗ y) ⊕ (x ⊗ z))
        ((x ⊗ y) ⊕ (x ⊗ z))
        (inv (snd (distributiveL KA-has-KleeneCatStr x y z)) ⋆⟨ KA-Cat ⟩
          fst (distributiveL KA-has-KleeneCatStr x y z))
        (Category.id KA-Cat)
    ret (snd (distributiveL KA-has-KleeneCatStr x y z)) =
     isPropHom-KA-Cat
       ((KA-MonoidalCat MonoidalCategory.⊗ x)
         (KA-Cat-BinCoproducts y z .binCoprodOb))
       ((KA-MonoidalCat MonoidalCategory.⊗ x)
         (KA-Cat-BinCoproducts y z .binCoprodOb))
       ((fst (distributiveL KA-has-KleeneCatStr x y z)) ⋆⟨ KA-Cat ⟩
         inv (snd (distributiveL KA-has-KleeneCatStr x y z)))
       (MonoidalCategory.C KA-MonoidalCat .Category.id)
    fst (distributiveR KA-has-KleeneCatStr x y z) =
      cong (λ a → a ⊕ ((y ⊗ x) ⊕ (z ⊗ x))) (⊗distR x y z) ∙
      ⊕idem ((y ⊗ x) ⊕ (z ⊗ x))
    inv (snd (distributiveR KA-has-KleeneCatStr x y z)) =
      cong (λ a → a ⊕ ((y ⊕ z) ⊗ x)) (sym (⊗distR x y z)) ∙
      ⊕idem ((y ⊕ z) ⊗ x)
    sec (snd (distributiveR KA-has-KleeneCatStr x y z)) =
      KA-is-poset .is-prop-valued
        ((y ⊗ x) ⊕ (z ⊗ x))
        ((y ⊗ x) ⊕ (z ⊗ x))
        (inv (snd (distributiveR KA-has-KleeneCatStr x y z)) ⋆⟨ KA-Cat ⟩
          fst (distributiveR KA-has-KleeneCatStr x y z))
        (KA-Cat .Category.id)
    ret (snd (distributiveR KA-has-KleeneCatStr x y z)) =
      KA-is-poset .is-prop-valued
       ((y ⊕ z) ⊗ x)
       ((y ⊕ z) ⊗ x)
       (fst (distributiveR KA-has-KleeneCatStr x y z) ⋆⟨ KA-Cat ⟩
         inv (snd (distributiveR KA-has-KleeneCatStr x y z)))
       (KA-Cat .Category.id)
    FAlgebra.carrier (fst (initialF KA-has-KleeneCatStr a b)) =
      (star a) ⊗ b
    FAlgebra.algebra (fst (initialF KA-has-KleeneCatStr a b)) =
      cong (λ c → (b ⊕ c) ⊕ (star a ⊗ b)) (sym (⊗assoc a (star a) b)) ∙
      cong (λ c → (c ⊕ ((a ⊗ star a) ⊗ b)) ⊕ (star a ⊗ b))  (sym (⊗unitL b)) ∙
      cong (λ c → c ⊕ (star a ⊗ b)) (sym (⊗distR b unitKA (a ⊗ star a))) ∙
      sym (⊗distR b (unitKA ⊕ (a ⊗ star a)) (star a)) ∙
      cong (λ c → c ⊗ b) (one-plus-starR a)
    fst (fst (snd (initialF KA-has-KleeneCatStr a b) y)) =
      star-inL a b (y .FAlgebra.carrier) (y .FAlgebra.algebra)
    snd (fst (snd (initialF KA-has-KleeneCatStr a b) y)) =
     isPropHom-KA-Cat
       ((F-Functor KA-MonoidalCat KA-Cat-BinCoproducts a b) .F-ob
         (fst (initialF KA-has-KleeneCatStr a b)
         .FAlgebra.carrier))
       (FAlgebra.carrier y)
       (seq' (MonoidalCategory.C KA-MonoidalCat)
         (F-Functor KA-MonoidalCat KA-Cat-BinCoproducts a b .F-hom
          (fst (fst (snd (initialF KA-has-KleeneCatStr a b) y))))
         (y .FAlgebra.algebra))
       (seq' (MonoidalCategory.C KA-MonoidalCat)
         (fst (initialF KA-has-KleeneCatStr a b) .FAlgebra.algebra)
         (fst (fst (snd (initialF KA-has-KleeneCatStr a b) y))))
    snd (snd (initialF KA-has-KleeneCatStr a b) y) z =
      Σ≡Prop
        (λ x → KA-Cat .Category.isSetHom
          (seq' (MonoidalCategory.C KA-MonoidalCat)
        (F-Functor KA-MonoidalCat KA-Cat-BinCoproducts a b .F-hom x)
        (y .FAlgebra.algebra))
        (seq' (MonoidalCategory.C KA-MonoidalCat)
          (fst (initialF KA-has-KleeneCatStr a b)
          .FAlgebra.algebra) x))
        (isPropHom-KA-Cat
          (FAlgebra.carrier (fst (initialF KA-has-KleeneCatStr a b)))
          (FAlgebra.carrier y)
          (fst (snd (initialF KA-has-KleeneCatStr a b) y) .fst)
          (z .fst))
    initialG KA-has-KleeneCatStr = {!!}
    F-with-unit-iso KA-has-KleeneCatStr = {!!}
    G-with-unit-iso KA-has-KleeneCatStr = {!!}
