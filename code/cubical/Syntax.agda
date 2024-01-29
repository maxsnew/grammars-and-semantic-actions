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

module Syntax ℓ (Σ₀ : Sig₀ ℓ) where
  record IntuitCtx {L : Level} : Type (ℓ-suc L) where
    field
      intuit-var : Type
      isFinSetIntuitVar : isFinSet intuit-var
      el : intuit-var → Type L

    intuitVarFinSet : FinSet ℓ-zero
    intuitVarFinSet = intuit-var , isFinSetIntuitVar

    liftCtx : {L' : Level} → IntuitCtx {L'}
    intuit-var (liftCtx) = Lift intuit-var
    isFinSetIntuitVar (liftCtx) = {!LiftIso!}
    el (liftCtx) = {!!}

  open IntuitCtx

  empty-intuit-ctx : IntuitCtx {ℓ-zero}
  empty-intuit-ctx .intuit-var = ⊥
  empty-intuit-ctx .isFinSetIntuitVar = isFinSetFin
  empty-intuit-ctx .el = λ ()

  singleton-intuit-ctx : (A : Type ℓ) → IntuitCtx
  singleton-intuit-ctx A .intuit-var = Unit
  singleton-intuit-ctx A .isFinSetIntuitVar = isFinSetUnit
  singleton-intuit-ctx A .el _ = A

  append-intuit-ctx : {L : Level} → IntuitCtx {L} → IntuitCtx {L} → IntuitCtx {L}
  append-intuit-ctx Γ Δ .intuit-var = Γ .intuit-var ⊎ Δ .intuit-var
  append-intuit-ctx Γ Δ .isFinSetIntuitVar = isFinSet⊎ (intuitVarFinSet Γ) (intuitVarFinSet Δ)
  append-intuit-ctx Γ Δ .el (inl x₁) = Γ .el x₁
  append-intuit-ctx Γ Δ .el (inr x₂) = Δ .el x₂

  data Grammar {Γ : IntuitCtx} {L : Level} : Type (ℓ-suc ℓ)
  data isStrictlyPositiveGrammar {Γ : IntuitCtx} {L : Level} : Grammar {Γ} {L} → Set (ℓ-suc ℓ)

  data Grammar {Γ} {L} where
    ILin : Grammar
    _⊗_ : Grammar {Γ} {L} → Grammar {Γ} {L} → Grammar {Γ} {L}
    literal : Σ₀ .fst → Grammar
    _-⊗_ : Grammar {Γ}{L} → Grammar {Γ}{L} → Grammar{Γ}{L}
    _⊗-_ : Grammar {Γ}{L} → Grammar {Γ}{L} → Grammar{Γ}{L}
    ΠLin : (x : Γ .intuit-var) → Grammar {append-intuit-ctx Γ (singleton-intuit-ctx (Γ .el x))} {L} → Grammar {Γ} {L}
    ΣLin : (x : Γ .intuit-var) → Grammar {append-intuit-ctx Γ (singleton-intuit-ctx (Γ .el x))} {L} → Grammar {Γ} {L}
    ⊤Lin : Grammar
    _&_ : Grammar {Γ}{L} → Grammar {Γ}{L} → Grammar {Γ}{L}
    KL* : Grammar {Γ}{L} → Grammar {Γ}{L}
    -- μ : (x : Type (ℓ-suc ℓ)) → Grammar {append-intuit-ctx Γ (singleton-intuit-ctx x)} {L} → Grammar {Γ} {L}
    -- TODO skirt around strict positivity restriction for μ?

  data isStrictlyPositiveGrammar {Γ} {L} where

  LinCtx : (Γ : IntuitCtx {ℓ}) → Type (ℓ-suc ℓ)
  LinCtx Γ = List (Grammar {Γ} {ℓ-suc ℓ})

  record Ctx : Type (ℓ-max ℓ (ℓ-suc ℓ)) where
    field
      intuit : IntuitCtx {ℓ}
      lin : LinCtx intuit

  open Ctx

  mkCtx : (Γ : IntuitCtx {ℓ}) → List (Grammar {Γ} {ℓ-suc ℓ}) → Ctx
  mkCtx Γ Δ .intuit = Γ
  mkCtx Γ Δ .lin = Δ

  data _⊢_ : (Δ : Ctx) → Grammar {Δ .intuit} {ℓ-suc ℓ} → Type (ℓ-suc ℓ) where
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

    -- μ-intro
    -- μ-elim

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
  KL*-elimL : ∀ {Γ : IntuitCtx} {g g' : Grammar} {Δ : LinCtx Γ} →
      (e : mkCtx Γ Δ ⊢ KL* g) →
      (mkCtx Γ [] ⊢ g') →
      (mkCtx Γ ([ g' ] ++ [ g ]) ⊢ g') →
      (mkCtx Γ (Δ) ⊢ g')
  KL*-elimL {Γ} {g}{g'} {Δ} e e₀ e' =
    -⊗-elim
      (KL*-elimR
        e
        (-⊗-intro identity)
        (-⊗-intro (substL e' (-⊗-elim identity identity)))
      )
      e₀

module _ where
  data αβ : Set where
    a : αβ
    b : αβ

  isSetαβ : isSet αβ
  isSetαβ = {!!}

  open Syntax ℓ-zero (αβ , isSet→isGroupoid isSetαβ)
  int : IntuitCtx
  int = empty-intuit-ctx

  testLinCtx : LinCtx int
  testLinCtx = [ literal a ] ++ [ literal b ] ++ [ literal a ] ++ [ literal b ] ++ [ literal a ]

  g : Grammar {int} {ℓ}
  g = KL*(literal a ⊗ literal b) ⊗ literal a

  -- a hand parse that "ababa" matches "(ab)* ⊗ a"
  test : mkCtx int testLinCtx ⊢ g
  test =
    ⊗-intro {Δ = testLinCtx}(KL*-cons {int}{literal a ⊗ literal b}
                      {Δ = [ literal a ] ++ [ literal b ]}
                      {Δ' = [ literal a ] ++ [ literal b ]}
                      (⊗-intro {Δ = [ literal a ] ++ [ literal b ]}
                               {Δ₁ = [ literal a ]}
                               {Δ₂ = [ literal b ]} identity identity)
                               (KL*-cons ((⊗-intro {Δ = [ literal a ] ++ [ literal b ]}
                               {Δ₁ = [ literal a ]}
                               {Δ₂ = [ literal b ]} identity identity)) (KL*-empty I-intro))) (identity {g = literal a})
