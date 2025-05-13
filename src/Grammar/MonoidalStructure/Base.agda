{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.MonoidalStructure.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.List.Base
open import Erased.Lift.Base

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓX ℓ : Level
    A A1 : Grammar ℓA
    B A2 : Grammar ℓB
    C A3 : Grammar ℓC
    D A4 : Grammar ℓD
    E A5 : Grammar ℓE
    F A6 : Grammar ℓF
    f f' f'' : A ⊢ B

open StrongEquivalence
record MonoidalStr ℓA : Type (ℓ-suc ℓA) where
  field
    ε : Grammar ℓA
    ε-intro : ε []
    ε-elim : ∀ {A : Grammar ℓA} → A [] → ε ⊢ A

    literal : Alphabet → Grammar ℓ-zero
    lit-intro : {c : Alphabet} → literal c [ c ]

    _⊗_ : Grammar ℓA → Grammar ℓA →  Grammar ℓA
    ⊗-intro : A ⊢ B → C ⊢ D → A ⊗ C ⊢ B ⊗ D
    @0 ⊗-intro∘g⊗-intro : ∀ {f : A ⊢ B} {f' : C ⊢ D} {f'' : B ⊢ E} {f''' : D ⊢ F} →
      ⊗-intro f'' f''' ∘g ⊗-intro f f' ≡ ⊗-intro (f'' ∘g f) (f''' ∘g f')
    @0 id⊗id≡id : ⊗-intro {A = A} {C = B} id id ≡ id

    mk⊗ : ∀ {w w' : String} → A w → B w' → (A ⊗ B) (w ++ w')

    ⊗-unit-r : A ⊗ ε ⊢ A
    ⊗-unit-r⁻ : A ⊢ A ⊗ ε
    @0 ⊗-unit-rr⁻ : ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
    @0 ⊗-unit-r⁻r : ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id

    ⊗-unit-l : ε ⊗ A ⊢ A
    ⊗-unit-l⁻ : A ⊢ ε ⊗ A
    @0 ⊗-unit-ll⁻ : ⊗-unit-l⁻ {A = A} ∘g ⊗-unit-l ≡ id
    @0 ⊗-unit-l⁻l : ⊗-unit-l {A = A} ∘g ⊗-unit-l⁻ ≡ id

    ⊗-assoc : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
    ⊗-assoc⁻ : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
    @0 ⊗-assoc∘⊗-assoc⁻≡id : ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
    @0 ⊗-assoc⁻∘⊗-assoc≡id : ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id

    _⟜_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
    ⟜-intro : A ⊗ B ⊢ C → B ⊢ C ⟜ A
    ⟜-app : A ⊗ (B ⟜ A) ⊢ B

    @0 ⟜-β : (e : (A ⊗ B) ⊢ C) → ⟜-app ∘g ⊗-intro id (⟜-intro e) ≡ e
    @0 ⟜-η : (f : A ⊢ B ⟜ C) → f ≡ ⟜-intro (⟜-app ∘g ⊗-intro id f)

    _⊸_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
    ⊸-intro : A ⊗ B ⊢  C → A ⊢ B ⊸ C
    ⊸-app : (A ⊸ B) ⊗ A ⊢ B

    @0 ⊸-β : (e : A ⊗ B ⊢ C) → ⊸-app ∘g ⊗-intro (⊸-intro e) id ≡ e
    @0 ⊸-η : (e : A ⊢ B ⊸ C) → ⊸-intro (⊸-app ∘g ⊗-intro e id) ≡ e

    ⊕ᴰ-distL : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA} →
      (⊕[ x ∈ X ] B x) ⊗ A ≅ ⊕[ x ∈ X ] (B x ⊗ A)

    @0 ⊕ᴰ-distL-β : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA} {x : X} →
      ⊕ᴰ-distL {A = A} {B = B} .fun ∘g ⊗-intro (σ x) id ≡ σ x

    @0 ⊕ᴰ-distL-β' : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA}
      {C : Grammar ℓA} {D : Grammar ℓA} →
      (f : (x : X) → B x ⊢ C) → (g : A ⊢ D) →
      ⊕ᴰ-elim (λ x → ⊗-intro (f x) g) ∘g ⊕ᴰ-distL {A = A} {B = B} .fun ≡ ⊗-intro (⊕ᴰ-elim f) g

    ⊕ᴰ-distR : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA} →
      A ⊗ (⊕[ x ∈ X ] B x) ≅ ⊕[ x ∈ X ] (A ⊗ B x)

    @0 ⊕ᴰ-distR-β : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA} {x : X} →
      ⊕ᴰ-distR {A = A} {B = B} .fun ∘g ⊗-intro id (σ x) ≡ σ x

    @0 ⊕ᴰ-distR-β' : ∀ {X : Type ℓA} {A : Grammar ℓA} {B : X → Grammar ℓA}
      {C : Grammar ℓA} {D : Grammar ℓA} →
      (f : (x : X) → B x ⊢ C) → (g : A ⊢ D) →
      ⊕ᴰ-elim (λ x → ⊗-intro g (f x)) ∘g ⊕ᴰ-distR {A = A} {B = B} .fun ≡ ⊗-intro g (⊕ᴰ-elim f)

  _,⊗_ = ⊗-intro

  ＂_＂ : Alphabet → Grammar ℓ-zero
  ＂ c ＂ = literal c

  infixr 25 _⊗_
  infixr 2 _⊸_
  infixl 2 _⟜_

  -- ε : Grammar ℓ
  -- ε {ℓ = ℓ} = LiftG ℓ ε

  ⟜-intro-ε : A ⊢ C → ε ⊢ C ⟜ A
  ⟜-intro-ε f = ⟜-intro (f ∘g ⊗-unit-r)

  ⊸-intro-ε : A ⊢ C → ε ⊢ A ⊸ C
  ⊸-intro-ε f = ⊸-intro (f ∘g ⊗-unit-l)

  ⟜-intro⁻ : A ⊢ B ⟜ C → C ⊗ A ⊢ B
  ⟜-intro⁻ f = ⟜-app ∘g id ,⊗ f

  ⊸-intro⁻ : A ⊢ B ⊸ C → A ⊗ B ⊢ C
  ⊸-intro⁻ {B = B}{C = C} f = ⊸-app ∘g ⊗-intro f (id {A = B})

  ⊸-mapCod : C ⊢ D → A ⊸ C ⊢ A ⊸ D
  ⊸-mapCod f = ⊸-intro (f ∘g ⊸-app)

  ⟜-mapCod : C ⊢ D → C ⟜ A ⊢ D ⟜ A
  ⟜-mapCod f = ⟜-intro (f ∘g ⟜-app)

  ⊸-mapDom : A ⊢ B → B ⊸ C ⊢ A ⊸ C
  ⊸-mapDom f = ⊸-intro (⊸-app ∘g id ,⊗ f)

  ⟜-mapDom : A ⊢ B → C ⟜ B ⊢ C ⟜ A
  ⟜-mapDom f = ⟜-intro (⟜-app ∘g f ,⊗ id)

  ⟜-curry : A ⟜ (B ⊗ C) ⊢ (A ⟜ B) ⟜ C
  ⟜-curry {A = A} = ⟜-intro (⟜-intro {C = A}(⟜-app ∘g ⊗-assoc))

  ⊸-curry : (A ⊗ B) ⊸ C ⊢ A ⊸ (B ⊸ C)
  ⊸-curry {C = C} = ⊸-intro (⊸-intro (⊸-app ∘g ⊗-assoc⁻))

  ⊸2-intro-ε : A1 ⊗ A2 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ C
  ⊸2-intro-ε {C = C} f = ⊸-curry ∘g ⊸-intro-ε f

  ⊸3-intro-ε : A1 ⊗ A2 ⊗ A3 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C
  ⊸3-intro-ε {C = C} f = ⊸-mapCod (⊸-curry {C = C}) ∘g ⊸2-intro-ε f

  ⊸4-intro-ε : A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C
  ⊸4-intro-ε {C = C} f = ⊸-mapCod (⊸-mapCod (⊸-curry {C = C})) ∘g ⊸3-intro-ε f

  ⊸5-intro-ε : A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ A5 ⊢ C → ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ A5 ⊸ C
  ⊸5-intro-ε {C = C} f = ⊸-mapCod (⊸-mapCod (⊸-mapCod ⊸-curry)) ∘g ⊸4-intro-ε f

  -- applying a multi-argument function to the front of a substitution
  ⊸-app-l : (A ⊸ B) ⊗ A ⊗ D ⊢ B ⊗ D
  ⊸-app-l = (⊗-intro ⊸-app id ∘g ⊗-assoc)

  ⊸0⊗ : ε ⊢ C → D ⊢ C ⊗ D
  ⊸0⊗ f = f ,⊗ id ∘g ⊗-unit-l⁻

  ⊸1⊗ : ε ⊢ A1 ⊸ C → A1 ⊗ B ⊢ C ⊗ B
  ⊸1⊗ f = ⊸-app-l ∘g ⊸0⊗ f

  ⊸2⊗ : ε ⊢ A1 ⊸ A2 ⊸ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
  ⊸2⊗ f = ⊸-app-l ∘g ⊸1⊗ f

  ⊸2⊗' : A1 ⊗ A2 ⊢ C → A1 ⊗ A2 ⊗ D ⊢ C ⊗ D
  ⊸2⊗' f = f ,⊗ id ∘g ⊗-assoc

  ⊸3⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ D ⊢ C ⊗ D
  ⊸3⊗ f = ⊸-app-l ∘g ⊸2⊗ f

  ⊸4⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ D ⊢ C ⊗ D
  ⊸4⊗ f = ⊸-app-l ∘g ⊸3⊗ f

  ⊸5⊗ : ε ⊢ A1 ⊸ A2 ⊸ A3 ⊸ A4 ⊸ A5 ⊸ C → A1 ⊗ A2 ⊗ A3 ⊗ A4 ⊗ A5 ⊗ D ⊢ C ⊗ D
  ⊸5⊗ f = ⊸-app-l ∘g ⊸4⊗ f

  ⟜0⊗ : ε ⊢ C → D ⊢ D ⊗ C
  ⟜0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻

  open StrongEquivalence
  module _
    {A B C D : Grammar ℓA}
    (A≅B : A ≅ B) (C≅D : C ≅ D)
    where

    private
      the-fun : A ⊗ C ⊢ B ⊗ D
      the-fun = A≅B .fun ,⊗ C≅D .fun

      the-inv : B ⊗ D ⊢ A ⊗ C
      the-inv = A≅B .inv ,⊗ C≅D .inv

      @0 the-sec : the-fun ∘g the-inv ≡ id
      the-sec =
        ⊗-intro∘g⊗-intro
        ∙ (λ i → A≅B .sec i ,⊗ C≅D .sec i)
        ∙ id⊗id≡id

      @0 the-ret : the-inv ∘g the-fun ≡ id
      the-ret =
        ⊗-intro∘g⊗-intro
        ∙ (λ i → A≅B .ret i ,⊗ C≅D .ret i)
        ∙ id⊗id≡id

    ⊗≅ : (A ⊗ C) ≅ (B ⊗ D)
    ⊗≅ .fun = the-fun
    ⊗≅ .inv = the-inv
    ⊗≅ .sec = the-sec
    ⊗≅ .ret = the-ret


  module _
    {A B C : Grammar ℓA}
    where
    ⊗-assoc≅ : A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C
    ⊗-assoc≅ .fun = ⊗-assoc
    ⊗-assoc≅ .inv = ⊗-assoc⁻
    ⊗-assoc≅ .sec = ⊗-assoc∘⊗-assoc⁻≡id
    ⊗-assoc≅ .ret = ⊗-assoc⁻∘⊗-assoc≡id

  εr≅ : A ≅ A ⊗ ε
  εr≅ .fun = ⊗-unit-r⁻
  εr≅ .inv = ⊗-unit-r
  εr≅ .sec = ⊗-unit-rr⁻
  εr≅ .ret = ⊗-unit-r⁻r

  εl≅ : A ≅ ε ⊗ A
  εl≅ .fun = ⊗-unit-l⁻
  εl≅ .inv = ⊗-unit-l
  εl≅ .sec = ⊗-unit-ll⁻
  εl≅ .ret = ⊗-unit-l⁻l

  -- ⟜UMP : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}
  --   → Iso (A ⊗ B ⊢ C) (B ⊢ C ⟜ A)
  -- ⟜UMP {C = C} = {!!} -- iso ⟜-intro ⟜-intro⁻ (λ b → sym (⟜-η b)) ⟜-β
