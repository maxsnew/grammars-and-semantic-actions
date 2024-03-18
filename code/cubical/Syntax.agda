-- {-# OPTIONS --lossy-unification #-}
module Syntax where

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

data Any {L : Level} {A : Type L} (P : A → Type L) : List A → Type L where
  any : ∀ {x xs} → P x → Any P (x ∷ xs)
  any-∷ : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (λ y → x ≡ y) xs


Sig₀ : (ℓ : Level) → Type (ℓ-suc ℓ)
Sig₀ ℓ = hGroupoid ℓ

module Syntax (Σ₀ : Sig₀ ℓ-zero) where
  -- TODO order these for dependency
  -- shallowly embed intuitionstic contexts, deeply embed linear contexts
  record IntuitCtx {L : Level} : Type (ℓ-suc L) where
    field
      intuit-var : Type
      isFinSetIntuitVar : isFinSet intuit-var
      el : intuit-var → Type L

    intuitVarFinSet : FinSet ℓ-zero
    intuitVarFinSet = intuit-var , isFinSetIntuitVar

    -- liftCtx : {L' : Level} → IntuitCtx {L'}
    -- intuit-var (liftCtx) = Lift intuit-var
    -- isFinSetIntuitVar (liftCtx) = {!!}
    -- el (liftCtx) = {!!}

  open IntuitCtx

  empty-intuit-ctx : {L : Level} → IntuitCtx {L}
  empty-intuit-ctx .intuit-var = ⊥
  empty-intuit-ctx .isFinSetIntuitVar = isFinSetFin
  empty-intuit-ctx .el = λ ()

  singleton-intuit-ctx : {L : Level} (A : Type L) → IntuitCtx {L}
  singleton-intuit-ctx A .intuit-var = Unit
  singleton-intuit-ctx A .isFinSetIntuitVar = isFinSetUnit
  singleton-intuit-ctx A .el _ = A

  append-intuit-ctx : {L L' : Level} → IntuitCtx {L} → IntuitCtx {L'} → IntuitCtx {ℓ-max L L'}
  append-intuit-ctx Γ Δ .intuit-var = Γ .intuit-var ⊎ Δ .intuit-var
  append-intuit-ctx Γ Δ .isFinSetIntuitVar = isFinSet⊎ (intuitVarFinSet Γ) (intuitVarFinSet Δ)
  append-intuit-ctx {L}{L'} Γ Δ .el (inl x₁) = Lift {_}{ℓ-max L L'}(Γ .el x₁)
  append-intuit-ctx {L}{L'} Γ Δ .el (inr x₂) = Lift {_}{ℓ-max L L'}(Δ .el x₂)

  data Grammar  {L : Level} {Γ : IntuitCtx {L}} : Type L
  data StrictlyPositiveGrammar {L : Level} {Γ : IntuitCtx {L}} : Type L

  data Grammar {L}{Γ} where
    ILin : Grammar {L}{Γ}
    -- Var : Γ .intuit-var → Grammar {L}{Γ}
    _⊗_ : Grammar {L}{Γ} → Grammar {L}{Γ} → Grammar {L}{Γ}
    _⊕_ : Grammar {L}{Γ} → Grammar {L}{Γ} → Grammar {L}{Γ}
    literal : Σ₀ .fst → Grammar {L}{Γ}
    _-⊗_ : Grammar {L}{Γ} → Grammar {L}{Γ} → Grammar{L}{Γ}
    _⊗-_ : Grammar {L}{Γ} → Grammar {L}{Γ} → Grammar{L}{Γ}
    -- ΠLin : (X : Type L) → Grammar {L}{append-intuit-ctx Γ (singleton-intuit-ctx {L} {!!})} → Grammar {L}{Γ}
    -- ΣLin : (X : Type L) → Grammar {L}{append-intuit-ctx Γ (singleton-intuit-ctx {L} X)} → Grammar {L}{Γ}
    ⊤Lin : Grammar {L}{Γ}
    _&_ : Grammar {L}{Γ} → Grammar {L}{Γ} → Grammar {L}{Γ}
    KL* : Grammar {L}{Γ} → Grammar {L}{Γ}
    μ : (X : StrictlyPositiveGrammar {L}{Γ}) → StrictlyPositiveGrammar
          {L}{append-intuit-ctx Γ (singleton-intuit-ctx {L} (Grammar {L}{Γ}))} →
        Grammar {L}{Γ}
        -- μ X . A
        -- A{μ X . A / X} what is a subst here?
        -- Γ ⊢ A : LinTy, X ∈ Γ
        -- steal substs from Max
        -- connor mcbride green slime? intro/elim
  data StrictlyPositiveGrammar {L}{Γ} where
    ILin : StrictlyPositiveGrammar {L}{Γ}
    _⊗_ : StrictlyPositiveGrammar {L}{Γ} → StrictlyPositiveGrammar {L}{Γ} → StrictlyPositiveGrammar {L}{Γ}
    _⊕_ : StrictlyPositiveGrammar {L}{Γ} → StrictlyPositiveGrammar {L}{Γ} → StrictlyPositiveGrammar {L}{Γ}
    literal : Σ₀ .fst → StrictlyPositiveGrammar {L}{Γ}
    -- μ : (X : StrictlyPositiveGrammar {L}{Γ}) → StrictlyPositiveGrammar
          -- {L}{append-intuit-ctx Γ (singleton-intuit-ctx {L} (StrictlyPositiveGrammar {L}{Γ}))}
      -- → StrictlyPositiveGrammar {L}{Γ}

  inj-on-ctx : ∀ {L}{Γ}{Γ'} → Grammar {L}{Γ} → Grammar {L}{append-intuit-ctx {L}{L} Γ Γ'}
  inj-on-ctx {L} {Γ} {Γ'} g = {!!}

  strict-inj-on-ctx : ∀ {L}{Γ}{Γ'} → StrictlyPositiveGrammar {L}{Γ} → StrictlyPositiveGrammar {L}{append-intuit-ctx {L}{L} Γ Γ'}
  strict-inj-on-ctx {L} {Γ} {Γ'} g = {!!}

  Strict→Grammar : {L : Level}{Γ : IntuitCtx {L}} → StrictlyPositiveGrammar {L}{Γ} → Grammar {L}{Γ}
  Strict→Grammar ILin = ILin
  Strict→Grammar (g₁ ⊗ g₂) = Strict→Grammar g₁ ⊗ Strict→Grammar g₂
  Strict→Grammar (g₁ ⊕ g₂) = Strict→Grammar g₁ ⊕ Strict→Grammar g₂
  Strict→Grammar (literal x) = literal x
  -- Strict→Grammar {L}{Γ} (μ X g) = μ X ?

  -- evalμ : {L : Level}{Γ : IntuitCtx {L}} → Grammar {L}{Γ} → Grammar {L}{Γ}
  -- evalμ {L} {Γ} (μ X g) = {!x!}
  -- evalμ {L} {Γ} x = x

  -- {-# TERMINATING #-}
  KL*μ : ∀ {L}{Γ}{X} → StrictlyPositiveGrammar {L}{Γ} → Grammar {L}{Γ}
  KL*μ {L}{Γ}{X} g =
    μ X (ILin ⊕ (strict-inj-on-ctx (g ⊗ X)))

  LinCtx : {L : Level}(Γ : IntuitCtx {L}) → Type L
  LinCtx {L} Γ = List (Grammar {L}{Γ})

  record Ctx {L : Level} : Type (ℓ-suc L) where
    field
      intuit : IntuitCtx {L}
      lin : LinCtx intuit

  open Ctx

  mkCtx : {L : Level}(Γ : IntuitCtx {L}) → List (Grammar {L}{Γ}) → Ctx
  mkCtx Γ Δ .intuit = Γ
  mkCtx Γ Δ .lin = Δ

  data _⊢_ {L : Level} : (Δ : Ctx) → Grammar {L}{Δ .intuit} → Type (ℓ-suc L) where
    identity : ∀ {Γ : IntuitCtx} {g : Grammar} → mkCtx Γ [ g ] ⊢ g

    linTyEq : ∀ {Γ : IntuitCtx} {g g' : Grammar} → g ≡ g' → mkCtx Γ [ g ] ⊢ g' → mkCtx Γ [ g' ] ⊢ g

    I-intro : ∀ {Γ : IntuitCtx} → mkCtx Γ [] ⊢ ILin
    I-elim : ∀ {Γ : IntuitCtx} {Δ Δ₁ Δ₂ : LinCtx Γ} {g : Grammar} →
      (e : (mkCtx Γ Δ) ⊢ ILin) →
      (e' : mkCtx Γ (Δ₁ ++ Δ₂) ⊢ g) →
      (mkCtx Γ (Δ₁ ++ Δ ++ Δ₂) ⊢ g)

    ⊗-intro : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ Δ₁ Δ₂ : LinCtx Γ} →
        (e : mkCtx Γ Δ₁ ⊢ g) →
        (e' : mkCtx Γ Δ₂ ⊢ g') →
        (mkCtx Γ (Δ₁ ++ Δ₂) ⊢ (g ⊗ g'))
    ⊗-elim : ∀ {Γ : IntuitCtx} {g g' g'' : Grammar} {Δ Δ₁ Δ₂ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ (g ⊗ g')) →
        (e' : mkCtx Γ (Δ₁ ++ [ g ] ++ [ g' ] ++ Δ₂) ⊢ g'') →
        (mkCtx Γ (Δ₁ ++ Δ ++ Δ₂) ⊢ g'')

    -⊗-intro : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ ([ g ] ++ Δ) ⊢ g') →
        (mkCtx Γ Δ ⊢ (g -⊗ g'))
    -⊗-elim : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ Δ' : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ (g -⊗ g')) →
        (e' : mkCtx Γ Δ' ⊢ g) →
        (mkCtx Γ (Δ' ++ Δ) ⊢ g')

    ⊗--intro : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
         (e : mkCtx Γ (Δ ++ [ g' ]) ⊢ g) →
         (mkCtx Γ Δ ⊢ (g ⊗- g'))
    ⊗--elim : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ Δ' : LinCtx Γ} →
         (e : mkCtx Γ Δ ⊢ (g ⊗- g')) →
         (e' : mkCtx Γ Δ' ⊢ g') →
         (mkCtx Γ (Δ ++ Δ') ⊢ g)

    -- ΠL-intro : ∀ {Γ : IntuitCtx} {g : Grammar} {X : Type ℓ}
      -- {Δ : LinCtx Γ}→
        -- (e : mkCtx (append-intuit-ctx Γ (singleton-intuit-ctx X)) Δ ⊢ g) →
        -- (mkCtx {!Γ!} Δ ⊢ {! (ΠLin X g) !})
    -- ΠL-elim : ∀ {Γ : IntuitCtx} {g : Grammar} {X : Type ℓ}
    -- ΣL-intro
    -- ΣL-elim

    ⊤L-intro : ∀ {Γ : IntuitCtx} {Δ : LinCtx Γ} →
      mkCtx Γ Δ ⊢ ⊤Lin

    &-intro : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ g) →
        (e' : mkCtx Γ Δ ⊢ g') →
        (mkCtx Γ Δ ⊢ (g & g'))
    &-elim₁ : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ (g & g')) →
        (mkCtx Γ Δ ⊢ g)
    &-elim₂ : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ (g & g')) →
        (mkCtx Γ Δ ⊢ g')

    -- μ-intro : ∀ {Γ : IntuitCtx} {g : Grammar} {Δ : LinCtx Γ} →
        -- (e : mkCtx Γ Δ ⊢ (μ g)) →
        -- (mkCtx Γ Δ ⊢ (μ g))
        --
        -- A{μX.A} ≡ Y
        -- e : Y
        -- -------
        -- cons e : μX.A
    -- μ-elim : {!!}

    KL*-empty : ∀ {Γ : IntuitCtx} {g : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ ILin) →
        (mkCtx Γ Δ ⊢ KL* g)
    KL*-cons : ∀ {Γ : IntuitCtx} {g : Grammar} {Δ Δ' : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ g) →
        (e' : mkCtx Γ Δ' ⊢ KL* g) →
        (mkCtx Γ (Δ ++ Δ') ⊢ KL* g)
    KL*-elimR : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
        (e : mkCtx Γ Δ ⊢ KL* g) →
        (mkCtx Γ [] ⊢ g') →
        (mkCtx Γ ([ g ] ++ [ g' ]) ⊢ g') →
        (mkCtx Γ Δ ⊢ g')

    substL : ∀ {Γ : IntuitCtx} {Δ Δ' : LinCtx Γ} {g g' : Grammar} →
        (e : mkCtx Γ Δ ⊢ g) →
        (e' : mkCtx Γ ([ g ] ++ Δ') ⊢ g') →
        (mkCtx Γ (Δ ++ Δ') ⊢ g')
    substR : ∀ {Γ : IntuitCtx} {Δ Δ' : LinCtx Γ} {g g' : Grammar} →
        (e : mkCtx Γ Δ' ⊢ g) →
        (e' : mkCtx Γ (Δ ++ [ g ]) ⊢ g') →
        (mkCtx Γ (Δ ++ Δ') ⊢ g')

  -- folding left over a Kleene star shown admissible in terms of folding right
  KL*-elimL : ∀ {L : Level} {Γ : IntuitCtx {L}} {g g' : Grammar} {Δ : LinCtx Γ} →
      (e : mkCtx Γ Δ ⊢ KL* g) →
      (mkCtx Γ [] ⊢ g') →
      (mkCtx Γ ([ g' ] ++ [ g ]) ⊢ g') →
      (mkCtx Γ (Δ) ⊢ g')
  KL*-elimL {Γ} {g}{g'} {Δ} e e₀ e' =
    -⊗-elim
      (KL*-elimR e
                 (-⊗-intro identity)
                 (-⊗-intro (substL {Δ = [ Δ ] ++ [ g' ]} e' (-⊗-elim identity identity))))
      e₀

module _ where
  data αβ : Set where
    a : αβ
    b : αβ

  isSetαβ : isSet αβ
  isSetαβ = {!!}

  open Syntax (αβ , isSet→isGroupoid isSetαβ)
  int : IntuitCtx {ℓ-zero}
  int = empty-intuit-ctx

  testLinCtx : LinCtx int
  testLinCtx = [ literal a ] ++ [ literal b ] ++ [ literal a ] ++ [ literal b ] ++ [ literal a ]

  g : Grammar {ℓ-zero}{int}
  g = KL*(literal a ⊗ literal b) ⊗ literal a

  -- a hand parse that "ababa" matches "(ab)* ⊗ a"
  test : mkCtx int testLinCtx ⊢ g
  test =
    ⊗-intro {Δ = testLinCtx}
      (KL*-cons
        (⊗-intro {Δ = [ literal a ] ++ [ literal b ]} identity identity)
        (KL*-cons (
          (⊗-intro {Δ = [ literal a ] ++ [ literal b ]} identity identity))
        (KL*-empty I-intro))) (identity)

  -- testμ : mkCtx int testLinCtx ⊢ ((KL*μ (literal a ⊗ literal b)) ⊗ literal a)
  -- testμ =
    -- ⊗-intro {Δ = testLinCtx}
     -- {!!}
     -- identity
