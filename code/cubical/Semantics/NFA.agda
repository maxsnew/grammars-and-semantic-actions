{-# OPTIONS #-}
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


module NFADefs ℓ (Σ₀ : hSet ℓ) where
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

    NFATrace-P : ∀ x → NFATrace-S x → Type
    NFATrace-P (state , word) (inl S) = ⊥
    NFATrace-P (state , word) (inr (inl (x , y))) = ⊤
    NFATrace-P (state , word) (inr (inr S)) = ⊤

    NFATrace-inX : ∀ x (s : NFATrace-S x) → NFATrace-P x s → NFATrace-X
    NFATrace-inX x (fsuc (inl (t , fibt))) _ = (N .dst (t .fst)) , (fibt .fst)
    NFATrace-inX x (fsuc (fsuc t)) _ = (N .ε-dst (t .fst)) , (x .snd)

    NFATrace→W :
      ∀ {s : N .Q .fst} {w : String} →
      NFATrace N s w → IW NFATrace-S NFATrace-P NFATrace-inX ((s , w))
    NFATrace→W nil =
      node (inl (refl , refl)) (λ ())
    NFATrace→W {s}{w} (cons {w'}{t} x) =
      node (inr (inl ((t , refl) , w' , refl)))
        (λ _ → NFATrace→W x)
    NFATrace→W {s}{w} (ε-cons {w'}{t} x) =
      node (inr (inr (t , refl)))
        (λ _ → NFATrace→W x)

    IWNFA = IW NFATrace-S NFATrace-P NFATrace-inX 

    W→NFATrace :
      ∀ {s : N .Q .fst} {w : String} →
      IW NFATrace-S NFATrace-P NFATrace-inX ((s , w)) → NFATrace N s w
    W→NFATrace (node (inl x) subtree) =
      transport
        (sym (cong₂ (λ a b → NFATrace N a b)
          (x .fst) (x .snd)))
        (NFATrace.nil {N = N})
    W→NFATrace (node (fsuc (inl x)) subtree) =
      transport
        (cong₂ (λ a b → NFATrace N a b)
          (x .fst .snd) (x .snd .snd))
        (NFATrace.cons {N = N} (W→NFATrace (subtree _)))
    W→NFATrace {s}{w} (node (fsuc (fsuc x)) subtree) =
      transport
        (cong (λ a → NFATrace N a w) (x .snd))
        (NFATrace.ε-cons {N = N} (W→NFATrace (subtree _)))

    NFATraceRetractofW : ∀ {s}{w} (tr : NFATrace N s w) →
      W→NFATrace (NFATrace→W tr) ≡ tr
    NFATraceRetractofW nil = transportRefl nil
    NFATraceRetractofW (cons tr) =
      transportRefl (cons (W→NFATrace (NFATrace→W tr))) ∙
      cong (λ a → cons a) (NFATraceRetractofW tr)
    NFATraceRetractofW (ε-cons tr) =
      transportRefl (ε-cons (W→NFATrace (NFATrace→W tr))) ∙
      cong (λ a → ε-cons a) (NFATraceRetractofW tr)

    isSetNFATrace-S : ∀ s w → isSet (NFATrace-S (s , w))
    isSetNFATrace-S s w =
      isSet⊎
        (isSet×
          (isSet→isGroupoid
            (isFinSet→isSet (N .Q .snd)) _ _)
          (isGroupoidString _ _))
        (isSet⊎
          (isSetΣ
            (isSetΣ (isFinSet→isSet (N .transition .snd))
            (λ t → isSet→isGroupoid (isFinSet→isSet (N .Q .snd)) _ _))
            λ fib → isSetΣ isSetString
              (λ w' → isGroupoidString _ _))
          (isSetΣ (isFinSet→isSet (N .ε-transition .snd))
            (λ t → isSet→isGroupoid
              (isFinSet→isSet (N .Q .snd)) _ _)))

    isSetNFATrace :
      (state : N .Q .fst) →
      (w : String) → isSet (NFATrace N state w)
    isSetNFATrace s w =
      isSetRetract
        NFATrace→W
        W→NFATrace
        NFATraceRetractofW
        (isOfHLevelSuc-IW 1
          (λ x → isSetNFATrace-S (x .fst) (x .snd))
          ((s , w)))

  open isSetNFATraceProof
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


