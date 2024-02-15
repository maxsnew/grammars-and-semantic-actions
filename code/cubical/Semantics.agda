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
open import Cubical.Data.Empty.Base
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

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.Instances.FreeComMonoid

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
  isSetKL*Ty g w = ?

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



  record NFA : Type (ℓ-suc ℓ) where
    constructor mkNFA
    field
      Q : FinSet ℓ
      init : Q .fst
      acc : Q .fst
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀ .fst
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst

  open NFA

  data NFATrace (N : NFA) : (state : N .Q .fst) → (w : String) → Type ℓ where
    nil : NFATrace N (N .acc) []
    cons :
      ∀ {w'} →
      {t : N .transition .fst} →
      NFATrace N (N .dst t) w' →
      NFATrace N (N .src t) (N .label t ∷ w')
    ε-cons :
      ∀ {w'} →
      {t : N .ε-transition .fst} →
      NFATrace N (N .ε-dst t) w' →
      NFATrace N (N .ε-src t) w'

  isSetNFATrace : (N : NFA) → (state : N .Q .fst) → (w : String) → isSet (NFATrace N state w)
  isSetNFATrace N = {!!}

  NFAGrammar : (N : NFA) → Grammar
  NFAGrammar N w = (NFATrace N (N .init) w) , isSetNFATrace N (N .init) w

  isFinSetLift :
    {L L' : Level} →
    {A : Type L} →
    isFinSet A → isFinSet (Lift {L}{L'} A)
  fst (isFinSetLift {A = A} isFinSetA) = isFinSetA .fst
  snd (isFinSetLift {A = A} isFinSetA) =
    Cubical.HITs.PropositionalTruncation.elim
    {P = λ _ → ∥ Lift A ≃ Fin (isFinSetA .fst) ∥₁}
    (λ [a] → isPropPropTrunc )
    (λ A≅Fin → ∣ compEquiv (invEquiv (LiftEquiv {A = A})) A≅Fin ∣₁)
    (isFinSetA .snd)

  literalNFA : (c : Σ₀ .fst) → NFA
  fst (Q (literalNFA c)) = Lift (Fin 2)
  snd (Q (literalNFA c)) = isFinSetLift isFinSetFin
  init (literalNFA c) = lift fzero
  acc (literalNFA c) = lift (fsuc fzero)
  transition (literalNFA c) = (Lift Unit) , (isFinSetLift isFinSetUnit)
  src (literalNFA c) (lift _) = literalNFA c .init
  dst (literalNFA c) (lift _) = literalNFA c .acc
  label (literalNFA c) (lift _) = c
  fst (ε-transition (literalNFA c)) = Lift ⊥
  snd (ε-transition (literalNFA c)) = isFinSetLift isFinSetFin
  ε-src (literalNFA c) (lift x) = ⊥.rec x
  ε-dst (literalNFA c) (lift x )= ⊥.rec x

  ⊗NFA : (N : NFA) → (N' : NFA) → NFA
  -- States stratified into init, N states, N' states, acc
  Q (⊗NFA N N') .fst = ⊤ ⊎ (N .Q .fst ⊎ ((N' .Q .fst) ⊎ ⊤))
  Q (⊗NFA N N') .snd =
    isFinSet⊎
      (_ , isFinSetUnit)
      (_ , (isFinSet⊎ (N .Q)
        (_ , (isFinSet⊎ (N' .Q) (_ , isFinSetUnit)))))
  -- initial state
  init (⊗NFA N N') = inl _
  -- accepting state
  acc (⊗NFA N N') = inr (inr (inr _))
  -- the labeled transitions come from N and N'
  transition (⊗NFA N N') .fst =
    N .transition .fst ⊎ N' .transition .fst
  transition (⊗NFA N N') .snd =
    isFinSet⊎ (N .transition) (N' .transition)
  -- the labeled transitions have same src, dst, and label as
  -- in original automata
  src (⊗NFA N N') (inl x) = inr (inl (N .src x))
  src (⊗NFA N N') (inr x) = inr (inr (inl (N' .src x)))
  dst (⊗NFA N N') (inl x) = inr (inl (N .dst x))
  dst (⊗NFA N N') (inr x) = inr (inr (inl (N' .dst x)))
  label (⊗NFA N N') (inl x) = N .label x
  label (⊗NFA N N') (inr x) = N' .label x
  -- 3 added ε-transitions + ones in subautomata
  fst (ε-transition (⊗NFA N N')) = Lift (Fin 3) ⊎ (N .ε-transition .fst ⊎ N' .ε-transition .fst)
  snd (ε-transition (⊗NFA N N')) =
   isFinSet⊎ {ℓ}
     (Lift (Fin 3) , isFinSetLift isFinSetFin)
     (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
  -- init to N init
  ε-src (⊗NFA N N') (inl (lift fzero)) = (⊗NFA N N') .init
  ε-dst (⊗NFA N N') (inl (lift fzero)) = inr (inl (N .init))
  -- N acc to N' init
  ε-src (⊗NFA N N') (inl (lift (fsuc fzero))) = inr (inl (N .acc))
  ε-dst (⊗NFA N N') (inl (lift (fsuc fzero))) = inr (inr (inl (N' .init)))
  -- N' acc to acc
  ε-src (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) = inr (inr (inl (N' .acc)))
  ε-dst (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) = (⊗NFA N N') .acc
  -- N ε-transitions
  ε-src (⊗NFA N N') (inr (inl x)) = inr (inl (N .ε-src x))
  ε-dst (⊗NFA N N') (inr (inl x)) = inr (inl (N .ε-dst x))
  -- N' ε-transitions
  ε-src (⊗NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-src x)))
  ε-dst (⊗NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-dst x)))

  ⊕NFA : (N : NFA) → (N' : NFA) → NFA
  -- States stratified into init, N states, N' states, acc
  Q (⊕NFA N N') .fst = ⊤ ⊎ (N .Q .fst ⊎ ((N' .Q .fst) ⊎ ⊤))
  Q (⊕NFA N N') .snd =
    isFinSet⊎
      (_ , isFinSetUnit)
      (_ , (isFinSet⊎ (N .Q)
        (_ , (isFinSet⊎ (N' .Q) (_ , isFinSetUnit)))))
  -- initial state
  init (⊕NFA N N') = inl _
  -- accepting state
  acc (⊕NFA N N') = inr (inr (inr _))
  -- the labeled transitions come from N and N'
  transition (⊕NFA N N') .fst =
    N .transition .fst ⊎ N' .transition .fst
  transition (⊕NFA N N') .snd =
    isFinSet⊎ (N .transition) (N' .transition)
  -- the labeled transitions have same src, dst, and label as
  -- in original automata
  src (⊕NFA N N') (inl x) = inr (inl (N .src x))
  src (⊕NFA N N') (inr x) = inr (inr (inl (N' .src x)))
  dst (⊕NFA N N') (inl x) = inr (inl (N .dst x))
  dst (⊕NFA N N') (inr x) = inr (inr (inl (N' .dst x)))
  label (⊕NFA N N') (inl x) = N .label x
  label (⊕NFA N N') (inr x) = N' .label x
  -- 4 ε-transitions + ones in subautomata
  fst (ε-transition (⊕NFA N N')) = Lift (Fin 4) ⊎ (N .ε-transition .fst ⊎ N' .ε-transition .fst)
  snd (ε-transition (⊕NFA N N')) =
    isFinSet⊎ {ℓ}
      (_ , isFinSetLift isFinSetFin)
      (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
  -- init to N init
  ε-src (⊕NFA N N') (inl (lift fzero)) = (⊕NFA N N') .init
  ε-dst (⊕NFA N N') (inl (lift fzero)) = inr (inl (N .init))
  -- init to N init
  ε-src (⊕NFA N N') (inl (lift (fsuc fzero))) = (⊕NFA N N') .init
  ε-dst (⊕NFA N N') (inl (lift (fsuc fzero))) = inr (inr (inl (N' .init)))
  -- N acc to acc
  ε-src (⊕NFA N N') (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .acc))
  ε-dst (⊕NFA N N') (inl (lift (fsuc (fsuc fzero)))) = (⊕NFA N N') .acc
  -- N' acc to acc
  ε-src (⊕NFA N N') (inl (lift (fsuc (fsuc (fsuc fzero))))) = inr (inr (inl (N' .acc)))
  ε-dst (⊕NFA N N') (inl (lift (fsuc (fsuc (fsuc fzero))))) = (⊕NFA N N') .acc
  -- N ε-transitions
  ε-src (⊕NFA N N') (inr (inl x)) = inr (inl (N .ε-src x))
  ε-dst (⊕NFA N N') (inr (inl x)) = inr (inl (N .ε-dst x))
  -- N' ε-transitions
  ε-src (⊕NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-src x)))
  ε-dst (⊕NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-dst x)))

  KL*NFA : (N : NFA) → NFA
  fst (Q (KL*NFA N)) = ⊤ ⊎ (N .Q .fst ⊎ ⊤)
  snd (Q (KL*NFA N)) =
    isFinSet⊎
      (_ , isFinSetUnit)
      (_ , isFinSet⊎ (N .Q) (_ , isFinSetUnit))
  init (KL*NFA N) = inl _
  acc (KL*NFA N) = inr (inr _)
  transition (KL*NFA N) = N .transition
  src (KL*NFA N) x = inr (inl (N .src x))
  dst (KL*NFA N) x = inr (inl (N .dst x))
  label (KL*NFA N) x = N .label x
  -- 4 ε-transitions + ones in subautomata
  fst (ε-transition (KL*NFA N)) = Lift (Fin 4) ⊎ (N .ε-transition .fst)
  snd (ε-transition (KL*NFA N)) =
    isFinSet⊎ {ℓ}
      (_ , isFinSetLift isFinSetFin)
      (N .ε-transition)
  -- init to N init
  ε-src (KL*NFA N) (inl (lift fzero)) = KL*NFA N .init
  ε-dst (KL*NFA N) (inl (lift fzero)) = inr (inl (N .init))
  -- init to acc
  ε-src (KL*NFA N) (inl (lift (fsuc fzero))) = KL*NFA N .init
  ε-dst (KL*NFA N) (inl (lift (fsuc fzero))) = KL*NFA N .acc
  -- N acc to N init
  ε-src (KL*NFA N) (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .acc))
  ε-dst (KL*NFA N) (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .init))
  -- N acc to acc
  ε-src (KL*NFA N) (inl (lift (fsuc (fsuc (fsuc fzero))))) = inr (inl (N .acc))
  ε-dst (KL*NFA N) (inl (lift (fsuc (fsuc (fsuc fzero))))) = KL*NFA N .acc
  -- N ε-transitions
  ε-src (KL*NFA N) (inr x) = inr (inl (N .ε-src x))
  ε-dst (KL*NFA N) (inr x) = inr (inl (N .ε-dst x))

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

  NFAαβ : NFA
  NFAαβ = ⊗NFA (literalNFA α) (literalNFA β)

  pNFAαβ : NFAGrammar NFAαβ (α ∷ β ∷ []) .fst
  pNFAαβ =
    ε-cons {t = inl (lift fzero)}
      (cons {t = inl _}
        (ε-cons {t = inl (lift (fsuc fzero))}
          (cons {t = inr _}
           (ε-cons {t = inl (lift (fsuc (fsuc fzero)))}
             nil))))
