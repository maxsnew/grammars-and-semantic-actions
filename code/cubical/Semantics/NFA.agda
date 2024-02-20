{-# OPTIONS --lossy-unification #-}
module Semantics.NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
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
open import Semantics.Grammar

private
  variable ℓ ℓ' : Level


module NFA ℓ (Σ₀ : hSet ℓ) where
  open GrammarDefs ℓ Σ₀ public

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

  module isSetNFATraceProof
    (N : NFA)
    where
    NFATrace-X = N .Q .fst × String
    NFATrace-S : NFATrace-X → Type ℓ
    NFATrace-S (s , w) =
      ((s ≡ N .acc) × (w ≡ [])) ⊎ (
      Σ (fiber (N .src) s) (λ t → fiber (λ w' → (N .label (t .fst)) ∷ w') w)  ⊎
      fiber (N .ε-src) s)

    NFATrace-P : ∀ x → NFATrace-S x → Type ℓ
    NFATrace-P (state , word) (inl S) = Lift ⊥
    NFATrace-P (state , word) (inr (inl (x , y))) =
      -- Σ (fiber (N .dst) state) λ t → t .fst ≡ x .fst
      Σ (N .Q .fst) λ st → st ≡ N .dst (x .fst)
    NFATrace-P (state , word) (inr (inr S)) =
      -- Σ (fiber (N .ε-dst) state) λ t → t .fst ≡ S .fst
      Σ (N .Q .fst) λ st → st ≡ N .ε-dst (S .fst)

    NFATrace-inX : ∀ x (s : NFATrace-S x) → NFATrace-P x s → NFATrace-X
    -- NFATrace-inX = {!!}
    NFATrace-inX (state , word) (inr (inl x)) f = f .fst , x .snd .fst
    NFATrace-inX (state , word) (inr (inr x)) f = (f .fst) , word

    NFATrace→W :
      ∀ {s : N .Q .fst} {w : String} →
      NFATrace N s w → IW NFATrace-S NFATrace-P NFATrace-inX ((s , w))
    NFATrace→W {.(N .acc)} {.[]} nil =
      node (inl (refl , refl)) (λ ())
    NFATrace→W {.(N .src _)} {.(N .label _ ∷ _)} (cons {w}{t} x) =
      node (inr (inl ((t , refl) , w , refl)))
        (λ p → NFATrace→W (subst (λ y → NFATrace N y w) (sym (p .snd)) x))
    NFATrace→W {.(N .ε-src _)} (ε-cons {w'}{t} x) =
      node (inr (inr (t , refl)))
        λ p → NFATrace→W (subst (λ y → NFATrace N y w') (sym (p .snd)) x)

    -- W→NFATrace : ∀ {s} {w} →
    --   IW NFATrace-S NFATrace-P NFATrace-inX ((s , w)) → NFATrace N s w
    -- W→NFATrace (node (inl x) subtree) =
    --   subst2 (λ a b → NFATrace N a b) (sym (x .fst)) (sym (x .snd)) (NFATrace.nil {N = N})
    -- W→NFATrace {s}{w} (node (fsuc (inl x)) subtree) =
    --   subst2 (λ a b → NFATrace N a b) {!x .fst .snd!} {!!}
    --     (W→NFATrace (subtree (N .dst (fst x .fst) , refl)))
    -- W→NFATrace {s}{w} (node (fsuc (fsuc x)) subtree) = {!!}

  isSetNFATrace :
    (N : NFA) → (state : N .Q .fst) →
    (w : String) → isSet (NFATrace N state w)
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

  emptyNFA : NFA
  Q emptyNFA = Lift (Fin 2) , isFinSetLift isFinSetFin
  init emptyNFA = lift fzero
  acc emptyNFA = lift (fsuc fzero)
  transition emptyNFA = Lift ⊥ , isFinSetLift isFinSetFin
  src emptyNFA (lift x) = ⊥.rec x
  dst emptyNFA (lift x) = ⊥.rec x
  label emptyNFA (lift x) = ⊥.rec x
  ε-transition emptyNFA = Lift Unit , isFinSetLift isFinSetUnit
  ε-src emptyNFA _ = emptyNFA .init
  ε-dst emptyNFA _ = emptyNFA .acc

  -- how to show that p must be ε-cons nil
  emptyNFA≡[] :
    ∀ {w} → NFATrace emptyNFA (emptyNFA .init) w → w ≡ []
  emptyNFA≡[] p = {!!}

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
  fst (ε-transition (⊗NFA N N')) =
    Lift (Fin 3) ⊎ (N .ε-transition .fst ⊎ N' .ε-transition .fst)
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
  ε-src (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) =
    inr (inr (inl (N' .acc)))
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
  fst (ε-transition (⊕NFA N N')) =
    Lift (Fin 4) ⊎ (N .ε-transition .fst ⊎ N' .ε-transition .fst)
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
  ε-src (⊕NFA N N') (inl (lift (fsuc (fsuc (fsuc fzero))))) =
    inr (inr (inl (N' .acc)))
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

-- TODO : Move this into another file after resolving all metas
module Thompson ℓ (Σ₀ : hSet ℓ) where
  open NFA ℓ Σ₀ public

  ILin-to-emptyNFA : ParseTransformer (ILin) (NFAGrammar emptyNFA)
  ILin-to-emptyNFA {w} p =
    subst
    (λ w' → NFAGrammar emptyNFA w' .fst)
    (sym p)
    (ε-cons nil)

  emptyNFA-to-NFA : ParseTransformer (NFAGrammar emptyNFA) ILin
  emptyNFA-to-NFA {w} p = {!p!}
