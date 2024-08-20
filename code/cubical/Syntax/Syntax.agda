-- {-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Syntax.Syntax where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

private
  variable ℓ ℓ' : Level

module Syntax (Σ₀ : Type) where
  data Grammar : Type (ℓ-suc ℓ-zero)
  data StrictlyPositiveGrammar : Type (ℓ-suc ℓ-zero)

  data Grammar where
    unit : Grammar
    Lin⊤ : Grammar
    Lin⊥ : Grammar
    literal : Σ₀ → Grammar
    _⊗_ : Grammar → Grammar → Grammar
    _⊕_ : Grammar → Grammar → Grammar
    _-⊗_ : Grammar → Grammar → Grammar
    _⊗-_ : Grammar → Grammar → Grammar
    LinΠ : {A : Type} → (A → Grammar) → Grammar
    LinΣ : {A : Type} → (A → Grammar) → Grammar
    μ : (X : StrictlyPositiveGrammar) → Grammar
    ⊗Assoc : ∀ {g h k} → g ⊗ (h ⊗ k) ≡ (g ⊗ h) ⊗ k

  data StrictlyPositiveGrammar where
    var : StrictlyPositiveGrammar
    _⊗literal_ : StrictlyPositiveGrammar → Σ₀ → StrictlyPositiveGrammar
    _literal⊗_ : Σ₀ → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕literal_ : StrictlyPositiveGrammar → Σ₀ → StrictlyPositiveGrammar
    _literal⊕_ : Σ₀ → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕unit : StrictlyPositiveGrammar → StrictlyPositiveGrammar
    unit⊕_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊗spg_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊕spg_ : StrictlyPositiveGrammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar
    _⊗l_ : Grammar → StrictlyPositiveGrammar → StrictlyPositiveGrammar

  eval-spg : StrictlyPositiveGrammar → Grammar → Grammar
  eval-spg var g = g
  eval-spg (x ⊗literal c) g =
    eval-spg x g ⊗ literal c
  eval-spg (c literal⊗ x) g =
    literal c ⊗ eval-spg x g
  eval-spg (x ⊕literal c) g =
    eval-spg x g ⊕ literal c
  eval-spg (c literal⊕ x) g =
    literal c ⊕ eval-spg x g
  eval-spg (x ⊕unit) g =
    eval-spg x g ⊕ unit
  eval-spg (unit⊕ x) g =
    unit ⊕ eval-spg x g
  eval-spg (x ⊗spg y) g =
    eval-spg x g ⊗ eval-spg y g
  eval-spg (x ⊕spg y) g =
    eval-spg x g ⊕ eval-spg y g
  eval-spg (x ⊗l y) g = x ⊗ eval-spg y g

  data Ctx : Type (ℓ-suc ℓ-zero) where
    mt : Ctx
    _,_ : Ctx → Grammar → Ctx

--   data OneHoleContext : Type (ℓ-suc ℓ-zero) where
--     var : OneHoleContext
--     _⊗l_ : OneHoleContext → Grammar → OneHoleContext
--     _⊗r_ : Grammar → OneHoleContext → OneHoleContext
--     _⊕l_ : OneHoleContext → Grammar → OneHoleContext
--     _⊕r_ : Grammar → OneHoleContext → OneHoleContext
--     _⊗OH_ : OneHoleContext → OneHoleContext → OneHoleContext
--     _⊕OH_ : OneHoleContext → OneHoleContext → OneHoleContext
--     _-⊗OH_ : Grammar → OneHoleContext → OneHoleContext
--     _⊗-OH_ : OneHoleContext → Grammar → OneHoleContext

--   evalOHContext : OneHoleContext → Grammar → Grammar
--   evalOHContext var g = g
--   evalOHContext (x ⊗l h) g = (evalOHContext x g) ⊗ h
--   evalOHContext (h ⊗r x) g = h ⊗ evalOHContext x g
--   evalOHContext (x ⊕l h) g = (evalOHContext x g) ⊕ h
--   evalOHContext (h ⊕r x) g = h ⊕ evalOHContext x g
--   evalOHContext (x ⊗OH y) g = (evalOHContext x g) ⊗ (evalOHContext y g)
--   evalOHContext (x ⊕OH y) g = (evalOHContext x g) ⊕ (evalOHContext y g)
--   evalOHContext (h -⊗OH x) g = h -⊗ (evalOHContext x g)
--   evalOHContext (x ⊗-OH h) g = (evalOHContext x g) ⊗- h

--   syntax evalOHContext Δ g = Δ [ g ]eval

  data _⊢_ : List Grammar → Grammar → Type (ℓ-suc ℓ-zero)
  data _~>_ : List Grammar → List Grammar → Type (ℓ-suc ℓ-zero)

  data _~>_ where
    mt-sub : ∀ {Δ} → [] ~> Δ
    mt-sub-uniq : ∀ {Δ} {δ : [] ~> Δ} → δ ≡ mt-sub
    id-sub : ∀ {Δ} → Δ ~> Δ
    extendl-sub : ∀ {Δ Δ'} {g} → Δ ⊢ g → (Δ ++ Δ') ~> ([ g ] ++ Δ')
    extendr-sub : ∀ {Δ Δ'} {g} → Δ ⊢ g → (Δ' ++ Δ) ~> (Δ' ++ [ g ])
    _∘*_ : ∀ {Δ Δ' Δ''} → Δ ~> Δ' → Δ' ~> Δ'' → Δ ~> Δ''
    ∘*id-l : ∀ {Δ Δ'} {δ : Δ ~> Δ'} → id-sub ∘* δ ≡ δ
    ∘*id-r : ∀ {Δ Δ'} {δ : Δ ~> Δ'} → δ ∘* id-sub ≡ δ
    ∘*assoc : ∀ {Δ Δ' Δ'' Δ'''}
      {δ : Δ ~> Δ'} →
      {δ' : Δ' ~> Δ''} →
      {δ'' : Δ'' ~> Δ'''} →
      δ ∘* (δ' ∘* δ'') ≡ (δ ∘* δ') ∘* δ''

  data _⊢_ where
    sub : ∀ {Δ Δ'} {g} (δ : Δ ~> Δ') → Δ' ⊢ g → Δ ⊢ g

    identity : ∀ {g} → [ g ] ⊢ g

    unit-I : [] ⊢ unit
    unit-E : ∀ {Δ Δ₁ Δ₂} {g} →
      Δ ⊢ unit →
      (Δ₁ ++ Δ₂) ⊢ g →
      (Δ₁ ++ Δ ++ Δ₂) ⊢ g
    unit-η : ∀ {Δ} → (e e' : Δ ⊢ unit) → e ≡ e'

    Lin⊤-I : ∀ {Δ} → Δ ⊢ Lin⊤
    Lin⊤-η : ∀ {Δ} → (e e' : Δ ⊢ Lin⊤) → e ≡ e'

    Lin⊥-E : ∀ {g} → [ Lin⊥ ] ⊢ g

    ⊗-I : ∀ {Δ₁ Δ₂} {g g'} →
      Δ₁ ⊢ g →
      Δ₂ ⊢ g' →
      (Δ₁ ++ Δ₂) ⊢ (g ⊗ g')
    ⊗-E : ∀ {Δ Δ₁ Δ₂} {g g' h} →
      Δ ⊢ (g ⊗ g') →
      (Δ₁ ++ [ g ] ++ [ g' ] ++ Δ₂) ⊢ h →
      (Δ₁ ++ Δ ++ Δ₂) ⊢ h

    ⊕-I₁ : ∀ {Δ} {g g'} →
      Δ ⊢ g →
      Δ ⊢ (g ⊕ g')
    ⊕-I₂ : ∀ {Δ} {g g'} →
      Δ ⊢ g' →
      Δ ⊢ (g ⊕ g')
    ⊕-E : ∀ {Δ} {g g' h} →
      Δ ⊢ (g ⊕ g') →
      [ g ] ⊢ h →
      [ g' ] ⊢ h →
      Δ ⊢ h

    -⊗-I : ∀ {Δ} {g h} →
      ([ g ] ++ Δ) ⊢ h →
      Δ ⊢ (g -⊗ h)
    -⊗-E : ∀ {Δ Δ'} {g h} →
      Δ ⊢ g →
      Δ' ⊢ (g -⊗ h) →
      (Δ ++ Δ') ⊢ h
    -⊗-β :
      ∀ {Δ Δ'} {g h} →
      (e : ([ g ] ++ Δ) ⊢ h) →
      (e' : Δ' ⊢ g) →
      -⊗-E e' (-⊗-I e) ≡
        sub
          (extendl-sub e')
          e
    -⊗-η :
      ∀ {Δ} {g h} →
      (e : Δ ⊢ (g -⊗ h)) →
      (-⊗-I (-⊗-E {g = g} {h = h} identity e)) ≡ e

    ⊗--I : ∀ {Δ} {g h} →
      (Δ ++ [ g ]) ⊢ h →
      Δ ⊢ (h ⊗- g)
    ⊗--E : ∀ {Δ Δ'} {g h} →
      Δ ⊢ (h ⊗- g) →
      Δ' ⊢ g →
      (Δ ++ Δ') ⊢ h
    ⊗--β :
      ∀ {Δ Δ'} {g h} →
      (e : (Δ ++ [ g ]) ⊢ h) →
      (e' : Δ' ⊢ g) →
      ⊗--E (⊗--I e) e' ≡ sub (extendr-sub e') e
    ⊗--η :
      ∀ {Δ} {g h} →
      (e : Δ ⊢ (g ⊗- h)) →
      ⊗--I (⊗--E e identity) ≡ e

    LinΠ-I : ∀ {Δ} {A : Type} → {f : A → Grammar} →
      (∀ a → Δ ⊢ f a) →
      Δ ⊢ LinΠ f
    LinΠ-E : ∀ {Δ} {A : Type} → {f : A → Grammar} →
      Δ ⊢ LinΠ f →
      (a : A) →
      Δ ⊢ f a
    LinΠ-β :
      ∀ {Δ} →
      {A : Type} → {f : A → Grammar} →
      (e : ∀ a → Δ ⊢ f a) →
      (e' : A) →
      LinΠ-E (LinΠ-I (λ a → e a)) e' ≡ e e'
    LinΠ-η :
      ∀ {Δ} →
      {A : Type} → {f : A → Grammar} →
      (e : Δ ⊢ LinΠ f) →
      e ≡ LinΠ-I (LinΠ-E e)


    LinΣ-I :
      ∀ {Δ} {A : Type} →
      {f : A → Grammar} →
      (a : A) →
      Δ ⊢ f a →
      Δ ⊢ LinΣ f
    LinΣ-E : ∀ {Δ} {g} {A : Type} → {f : A → Grammar} →
      Δ ⊢ LinΣ f →
      (∀ a → [ f a ] ⊢ g) →
      Δ ⊢ g
    LinΣ-β :
      ∀ {Δ} {A : Type} →
      {f : A → Grammar} →
      (a : A) →
      (e : Δ ⊢ f a) →
      LinΣ-E (LinΣ-I a e) (λ _ → identity) ≡ e
    -- can't access the witness from the term without helpers
    -- LinΣ-η :
    --   ∀ {Δ} {A : Type} →
    --   {f : A → Grammar} →
    --   (e : Δ ⊢ LinΣ f) →
    --   LinΣ-I {!!} (LinΣ-E e {!!}) ≡ e

    μ-I : ∀ {Δ} {g} →
      Δ ⊢ eval-spg g (μ g) →
      Δ ⊢ μ g
    μ-E : ∀ {Δ} {g} {h} →
      Δ ⊢ μ g →
      [ eval-spg g h ] ⊢ h →
      Δ ⊢ h
    -- μ-β :
    --   ∀ {Δ} {g h} →
    --   (e : Δ ⊢ eval-spg g (μ g)) →
    --   (e' : [ eval-spg g h ] ⊢ h) →
    --   μ-E (μ-I e) e' ≡ {!!}
    -- μ-η :
    --   ∀ {Δ} {g h} →
    --   (e : Δ ⊢ μ g) →
    --   (e' : [ eval-spg g h ] ⊢ h) →
    --   μ-I (μ-E e {!e'!}) ≡ e






  KL* : (g : Grammar) → Grammar
  KL* g = μ (unit⊕ (g ⊗l var))

module _ where
  data αβ : Type where
    a : αβ
    b : αβ
  open Syntax αβ

  g : Grammar
  g = KL* (literal a ⊗ literal b) ⊗ literal a

  test : map literal (a ∷ b ∷ a ∷ b ∷ a ∷ []) ⊢ g
  test =
    ⊗-I
      {Δ₁ = literal a ∷ literal b ∷ literal a ∷ literal b ∷ []}
      {Δ₂ = [ literal a ]}
      (μ-I
        (⊕-I₂
          (⊗-I
            {Δ₁ = literal a ∷ literal b ∷ []}
            {Δ₂ = literal a ∷ literal b ∷ []}
            (⊗-I identity identity)
            (μ-I
              (⊕-I₂
                (⊗-I
                  {Δ₁ = literal a ∷ literal b ∷ []}
                  {Δ₂ = []}
                  (⊗-I identity identity)
                  (μ-I (⊕-I₁ unit-I))))))))
      identity
