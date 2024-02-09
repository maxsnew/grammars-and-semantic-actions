{-# OPTIONS --lossy-unification #-}
module Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset

open import Cubical.Tactics.Reflection

private
  variable ℓ ℓ' : Level

module Semantics ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w = isSetΣ (isSet× isSetString isSetString) λ s → isGroupoidString w (s .fst ++ s .snd)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → hSet ℓ

  open ListPath
  ILin : Grammar
  ILin w = (w ≡ []) , isGroupoidString w []

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w = (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × g' (s .fst .snd) .fst) ,
    isSetΣ (isSetSplitting w) λ s → isSet× (g (s .fst .fst) .snd) (g' (s .fst .snd) .snd)

  literal : (Σ₀ .fst) → Grammar
  literal c w = ([ c ] ≡ w) , isGroupoidString ([ c ]) w

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w =
    (∀ (w' : String) → g w' .fst × g' (w' ++ w) .fst) ,
      isSetΠ (λ w' → isSet× (g w' .snd) (g' (w' ++ w) .snd))

  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w =
    (∀ (w' : String) → g (w ++ w') .fst × g' w' .fst) ,
      isSetΠ (λ w' → isSet× (g (w ++ w') .snd) (g' w' .snd))

  -- ΠLin : Grammar
  -- ΠLin :

  -- ΣLin : Grammar
  -- ΣLin :

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
      liftExt (isProp→isSet isProp⊥ (lower x) (lower y) (cong lower a) (cong lower b) i)

  _⇒_ : Grammar → Grammar → Grammar
  (g ⇒ g') w =
    (g w .fst → g' w .fst) ,
    isSetΠ (λ p → g' w .snd)

  ParseTransformer : Grammar → Grammar → Type ℓ
  ParseTransformer g g' = ∀ {w} → g w .fst → g' w .fst

  data KL*Ty (g : Grammar) (w : String) : Type ℓ where
    nil : ILin w .fst → (KL*Ty g w)
    cons : (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × KL*Ty g (s .fst .snd)) → KL*Ty g w

  isSetKL*Ty : (g : Grammar) → (w : String) → isSet (KL*Ty g w)
  isSetKL*Ty g w (nil a) (nil b) x y = {!!}
  isSetKL*Ty g w (nil a) (cons b) = {!!}
  isSetKL*Ty g w (cons a) (nil b) = {!!}
  isSetKL*Ty g w (cons a) (cons b) = {!!}

  KL* : (g : Grammar) → Grammar
  KL* g w = (KL*Ty g w , isSetKL*Ty g w)

  literal-or-empty : (Σ₀ .fst ⊎ ⊤) → (w : String) → Type ℓ
  literal-or-empty (inl c) w = (literal c) ([ c ]) .fst
  literal-or-empty (inr tt) w = ILin [] .fst

  unpack : (Σ₀ .fst ⊎ ⊤) → String
  unpack (inl c) = c ∷ []
  unpack (inr tt) = []

  isSetΣ₀⊎⊤ : isSet (Σ₀ .fst ⊎ ⊤)
  isSetΣ₀⊎⊤ = isSet⊎ (Σ₀ .snd) isSetUnit

  isPropLift : {ℓ' : Level} → {A : Type} → isProp A → isProp (Lift {ℓ-zero}{ℓ'} A)
  isPropLift isPropA x y =
    liftExt (isPropA (lower x) (lower y))

  data NFA
    (Q : FinSet ℓ)
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤))
    (init : Q .fst)
    (acc : Q .fst)
    : (state : Q .fst) → (w : String) → Type ℓ where
    nil : NFA Q δ init acc acc []
    cons :
      ∀ {w' s s' c} →
      (c ∈ δ s s') →
      literal-or-empty c w' →
      NFA Q δ init acc s' w' →
      NFA Q δ init acc s (unpack c ++ w')

  isSetNFA :
    (Q : FinSet ℓ) →
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (init : Q .fst) → (acc : Q .fst) →
    (s : Q .fst) → (w : String) → isSet (NFA Q δ init acc s w)
  isSetNFA Q δ init acc s w = {!!}

  NFAGrammar :
    (Q : FinSet ℓ) →
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (init : Q .fst) → (acc : Q .fst) → Grammar
  NFAGrammar Q δ init acc w =
    (NFA Q δ init acc init w , isSetNFA Q δ init acc init w)

  ⊗NFA :
    (Q Q' : FinSet ℓ) →
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (δ' : Q' .fst → Q' .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (init : Q .fst) →
    (init' : Q' .fst) →
    (acc : Q .fst) →
    (acc' : Q' .fst) →
    Grammar
  ⊗NFA Q Q' δ δ' init init' acc acc' x =
    NFAGrammar
      the-states
      the-δ
      the-init
      the-acc
      x
    where
    -- tag the states as start ⊎ Q ⊎ Q' ⊎ end
    the-states : FinSet ℓ
    fst the-states = ⊤ ⊎ (Q .fst ⊎ (Q' .fst ⊎ ⊤))
    snd the-states =
      isFinSet⊎ (_ , isFinSetUnit)
        (_ , (isFinSet⊎ Q (_ ,
          (isFinSet⊎ Q' ((_ , isFinSetUnit))))))

    the-δ : the-states .fst → the-states .fst → ℙ (Σ₀ .fst ⊎ ⊤)
    -- init ε-transition to first NFA's init
    the-δ (inl _) (inr (inl q')) x =
    -- no way to really pattern match and get that q' = init easily
      ((x ≡ inr _) × (q' ≡ init)) ,
        (isProp× (isSetΣ₀⊎⊤ _ _) (isFinSet→isSet (Q .snd) _ _))
    -- first NFA's transitions
    the-δ (inr (inl q)) (inr (inl q')) = δ q q'
    -- second NFA's transitions
    the-δ (inr (inr (inl q))) (inr (inr (inl q'))) = δ' q q'
    -- first NFA's acc to second NFA's init
    the-δ (inr (inl q)) (inr (inr (inl q'))) x =
      ((q ≡ acc) × (q' ≡ init') × (x ≡ inr _)) ,
      isProp×
      (isFinSet→isSet (Q .snd) _ _)
      (isProp× (isFinSet→isSet (Q' .snd) _ _) (isSetΣ₀⊎⊤ _ _))
    -- second NFA's acc to end
    the-δ (inr (inr (inl q))) (inr (inr (inr q'))) x =
      ((q ≡ acc') × (x ≡ inr _)) ,
      (isProp× (isFinSet→isSet (Q' .snd) _ _) (isSetΣ₀⊎⊤ _ _))
    -- No other transitions
    the-δ q q' x = (Lift ⊥) , (isPropLift isProp⊥)

    the-init : the-states .fst
    the-init = inl _

    the-acc : the-states .fst
    the-acc = inr (inr (inr _))

  ⊕NFA :
    (Q Q' : FinSet ℓ) →
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (δ' : Q' .fst → Q' .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (init : Q .fst) →
    (init' : Q' .fst) →
    (acc : Q .fst) →
    (acc' : Q' .fst) →
    Grammar
  ⊕NFA Q Q' δ δ' init init' acc acc' x =
    NFAGrammar
      the-states
      the-δ
      the-init
      the-acc
      x
    where
    the-states : FinSet ℓ
    fst the-states = ⊤ ⊎ (Q .fst ⊎ (Q' .fst ⊎ ⊤))
    snd the-states =
      isFinSet⊎ (_ , isFinSetUnit)
        (_ , (isFinSet⊎ Q (_ ,
          (isFinSet⊎ Q' ((_ , isFinSetUnit))))))

    the-δ : the-states .fst → the-states .fst → ℙ (Σ₀ .fst ⊎ ⊤)
    -- init ε-transition to first NFA's init
    the-δ (inl q) (inr (inl q')) x =
      ((x ≡ inr _) × (q' ≡ init)) ,
        (isProp× (isSetΣ₀⊎⊤ _ _) (isFinSet→isSet (Q .snd) _ _))
    -- init ε-transition to second NFA's init
    the-δ (inl q) (inr (inr (inl q'))) x =
      ((x ≡ inr _) × (q' ≡ init')) ,
        (isProp× (isSetΣ₀⊎⊤ _ _) (isFinSet→isSet (Q' .snd) _ _))
    -- first NFA's transitions
    the-δ (inr (inl q)) (inr (inl q')) = δ q q'
    -- second NFA's transitions
    the-δ (inr (inr (inl q))) (inr (inr (inl q'))) = δ' q q'
    -- first NFA's acc to end
    the-δ (inr (inl q)) (inr (inr (inr q'))) x =
      ((q ≡ acc) × (x ≡ inr _)) ,
      (isProp× (isFinSet→isSet (Q .snd) _ _) (isSetΣ₀⊎⊤ _ _))
    -- second NFA's acc to end
    the-δ (inr (inr (inl q))) (inr (inr (inr q'))) x =
      ((q ≡ acc') × (x ≡ inr _)) ,
      (isProp× (isFinSet→isSet (Q' .snd) _ _) (isSetΣ₀⊎⊤ _ _))
    -- No other transitions
    the-δ q q' x = (Lift ⊥) , (isPropLift isProp⊥)

    the-init : the-states .fst
    the-init = inl _

    the-acc : the-states .fst
    the-acc = inr (inr (inr _))

  KL*NFA :
    (Q : FinSet ℓ) →
    (δ : Q .fst → Q .fst → ℙ (Σ₀ .fst ⊎ ⊤)) →
    (init : Q .fst) →
    (acc : Q .fst) →
    Grammar
  KL*NFA Q δ init acc x =
    NFAGrammar
      the-states
      the-δ
      the-init
      the-acc
      x
    where
    the-states : FinSet ℓ
    fst the-states = ⊤ ⊎ (Q .fst ⊎ ⊤)
    snd the-states =
      isFinSet⊎
        (_ , isFinSetUnit)
        (_ , isFinSet⊎ Q (_ , isFinSetUnit))

    the-δ : the-states .fst → the-states .fst → ℙ (Σ₀ .fst ⊎ ⊤)
    -- init ε-transition to NFA's init
    the-δ (inl _) (inr (inl q')) x =
      ((x ≡ inr _) × (q' ≡ init)) ,
        (isProp× (isSetΣ₀⊎⊤ _ _) (isFinSet→isSet (Q .snd) _ _))
    -- init ε-transition to end
    the-δ (inl _) (inr (inr q')) x =
      ((x ≡ inr _)) ,
      (isSetΣ₀⊎⊤ _ _)
   -- first NFA's acc to end
    the-δ (inr (inl q)) (inr (inr q')) x =
      ((q ≡ acc) × (x ≡ inr _)) ,
      (isProp× (isFinSet→isSet (Q .snd) _ _) (isSetΣ₀⊎⊤ _ _))
    -- NFA's acc to init state
    -- TODO : initially this was written as NFA's acc to NFA's init state
    -- but that can't work with this pattern matching without some refactors
    -- this difference shouldn't matter
    the-δ (inr (inl q)) (inl _) x =
      ((x ≡ inr _) × (q ≡ acc)) ,
        (isProp× (isSetΣ₀⊎⊤ _ _) (isFinSet→isSet (Q .snd) _ _))
    -- first NFA's transitions
    the-δ (inr (inl q)) (inr (inl q')) = δ q q'
    -- No other transitions
    the-δ q q' x = (Lift ⊥) , (isPropLift isProp⊥)

    the-init : the-states .fst
    the-init = inl _

    the-acc : the-states .fst
    the-acc = (inr (inr _))

module _ where
  data αβ : Set ℓ-zero where
    α : αβ
    β : αβ

  isSetαβ : isSet αβ
  isSetαβ = {!!}

  open Semantics ℓ-zero (αβ , isSetαβ)
  word : String
  word = α ∷ β ∷ α ∷ β ∷ α ∷ []

  g : Grammar
  g = (KL* (literal α ⊗ literal β) ⊗ literal α)


  p : g word .fst
  p = ((α ∷ β ∷ α ∷ β ∷ [] , α ∷ []) , refl) ,
      cons (((α ∷ β ∷ [] , α ∷ β ∷ []) , refl) ,
           ((([ α ] , [ β ]) , refl) , (refl , refl)) ,
           (cons ((((α ∷ β ∷ []) , []) , refl) ,
             (((([ α ] , [ β ]) , refl) , (refl , refl)) , (nil refl))))) ,
      refl

  wα = α ∷ []
  wβ = β ∷ []

  pα : (literal α) wα .fst
  pα = refl

  NFAtransitions : (y : αβ) → (s s' : Fin 2) → ℙ (αβ ⊎ ⊤)
  NFAtransitions y fzero fzero x = ⊥ , isProp⊥
  NFAtransitions y fzero (fsuc fzero) x = (x ≡ (inl y)) , isSetΣ₀⊎⊤ _ _
  NFAtransitions y (fsuc fzero) fzero x = ⊥ , isProp⊥
  NFAtransitions y (fsuc fzero) (fsuc fzero) x = ⊥ , isProp⊥

  pNFAα :
    NFA
      (Fin 2 , isFinSetFin)
      (NFAtransitions α) fzero (fsuc fzero)
      fzero wα
  pNFAα = cons refl refl nil

  pNFAβ :
    NFA
      (Fin 2 , isFinSetFin)
      (NFAtransitions β) fzero (fsuc fzero)
      fzero wβ
  pNFAβ = cons refl refl nil

  α⊗βNFA : Grammar
  α⊗βNFA =
    ⊗NFA
      (Fin 2 , isFinSetFin)
      (Fin 2 , isFinSetFin)
      (NFAtransitions α)
      (NFAtransitions β)
      fzero
      fzero
      (fsuc fzero)
      (fsuc fzero)

  pNFAαβ : α⊗βNFA (α ∷ β ∷ []) .fst
  pNFAαβ =
    cons
      {s' = inr (inl fzero)}
      {c = inr _}
     (refl , refl)
     refl
     (cons
       {s' = inr (inl (fsuc fzero))}
       {c = inl α}
       refl
       refl
       (cons
         {s' = inr (inr (inl fzero))}
         {c = inr _}
         (refl , (refl , refl))
         refl
         (cons
           {s' = inr (inr (inl (fsuc fzero)))}
           {c = inl β}
           refl
           refl
           (cons
             {s' = inr (inr (inr tt))}
             {c = inr _}
             (refl , refl)
             refl
             nil
             ))))

  open Iso
